-- Prove2me | Theorems.Thm_ValuationSubring_exists_fractionRing_tensorProduct_quotient_algEquiv_apply_tmul_eq_coeffMap_of_residueField_ringEquiv
-- name    : ValuationSubring.exists_fractionRing_tensorProduct_quotient_algEquiv_apply_tmul_eq_coeffMap_of_residueField_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/f17c4794-b882-56b9-86bc-70757e387d33
-- title:
--   Fraction field of k⊗_A V identified with E'
-- statement:
--   Let $A$ be a commutative local ring with maximal ideal $\mathfrak m_A$ and residue field $\kappa =$ `IsLocalRing.ResidueField A`, and let $k$ be a field that is an $A$-algebra killing $\mathfrak m_A$ and also a $\kappa$-algebra whose structure map is compatible with the residue map $A \to \kappa$. Let $K$ be a field that is an $A$-algebra and $V \subseteq K$ a valuation subring containing the image of $A$, equipped with an $A$-algebra structure compatible with the inclusion $V \hookrightarrow K$. Assume $\mathfrak m_A = (\varpi)$ for some $\varpi \in A$, and that every $f \in K$ lying in `V.nonunits` can be written $f = \varpi g$ with $g \in V$. Let $E$ be an intermediate field of $\kappa \subseteq \kappa((q)) =$ `LaurentSeries` $\kappa$ and $\theta \colon V/\mathfrak m_V \xrightarrow{\sim} E$ a ring isomorphism sending the residue of $a \in A$ (viewed in $V$) to the image of the residue of $a$ in $E$. Assume that the coefficientwise map $\sigma =$ [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) associated with $\kappa \to k$, i.e. the ring homomorphism $\kappa((q)) \to k((q))$ applying $\kappa \to k$ to each coefficient, carries every $\kappa$-linearly independent finite family in $\kappa((q))$ to a $k$-linearly independent family in $k((q))$. Let $E'$ be an intermediate field of $k \subseteq k((q))$ equal to the field generated over $k$ by $\sigma(E)$, and let $\mathfrak q$ be a minimal prime of $k \otimes_A V$. Then there exists a $k$-algebra isomorphism $\Phi \colon \operatorname{Frac}\bigl((k \otimes_A V)/\mathfrak q\bigr) \xrightarrow{\sim} E'$ such that for every $v \in V$ the image under $\Phi$ of the fraction with numerator the class of $1 \otimes v$ and denominator $1$ equals, as a Laurent series over $k$, the coefficientwise image $\sigma(\theta(\bar v))$.
--
--   This is the identification of the generic residue fields of the base change $k \otimes_A V$ of a valuation ring along $A \to k$ with the coefficientwise base change $E'$ of a Laurent-series realisation $E$ of the residue field of $V$, in the sharpened form that also records the image of the pure tensors $1 \otimes v$. It is used in the construction of curve models for $X_1(p)$ and in the comparison of the components of their special fibres under the Gauss reading.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_fractionRing_tensorProduct_quotient_algEquiv_apply_tmul_eq_coeffMap_of_residueField_ringEquiv.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped TensorProduct

theorem ValuationSubring.exists_fractionRing_tensorProduct_quotient_algEquiv_apply_tmul_eq_coeffMap_of_residueField_ringEquiv
    (A : Type) [CommRing A] [IsLocalRing A]
    (k : Type) [Field k] [Algebra A k] (hk : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A k a = 0)
    [Algebra (IsLocalRing.ResidueField A) k]
    (hκk : ∀ a : A, algebraMap (IsLocalRing.ResidueField A) k (IsLocalRing.residue A a) = algebraMap A k a)
    {K : Type} [Field K] [Algebra A K]
    (V : ValuationSubring K) (hVA : ∀ a : A, algebraMap A K a ∈ V)
    [Algebra A ↥V] (halgV : ∀ a : A, ((algebraMap A ↥V a : ↥V) : K) = algebraMap A K a)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (hunif : ∀ f : K, f ∈ V.nonunits → ∃ g : K, g ∈ V ∧ f = algebraMap A K ϖ * g)
    (E : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)))
    (θ : IsLocalRing.ResidueField ↥V ≃+* ↥E)
    (hθ : ∀ a : A, θ (IsLocalRing.residue ↥V ⟨algebraMap A K a, hVA a⟩) =
      algebraMap (IsLocalRing.ResidueField A) ↥E (IsLocalRing.residue A a))
    (hLD : ∀ (n : ℕ) (f : Fin n → LaurentSeries (IsLocalRing.ResidueField A)),
      LinearIndependent (IsLocalRing.ResidueField A) f →
      LinearIndependent k (⇑(ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)) ∘ f))
    (E' : IntermediateField k (LaurentSeries k))
    (hE' : IntermediateField.adjoin k
      (⇑(ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)) '' ((E : Set (LaurentSeries (IsLocalRing.ResidueField A))))) = E')
    (𝔮 : Ideal (k ⊗[A] ↥V)) (h𝔮 : 𝔮 ∈ minimalPrimes (k ⊗[A] ↥V)) :
    ∃ Φ : FractionRing ((k ⊗[A] ↥V) ⧸ 𝔮) ≃ₐ[k] ↥E',
      ∀ v : ↥V,
        (((Φ (Localization.mk (Ideal.Quotient.mk 𝔮 ((1 : k) ⊗ₜ[A] v)) 1)) : ↥E') : LaurentSeries k)
          = ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)
              ((θ (IsLocalRing.residue ↥V v) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A)) := by sorry
