-- Prove2me | Theorems.Thm_ValuationSubring_nonempty_fractionRing_tensorProduct_quotient_algEquiv_of_residueField_ringEquiv_of_linearIndependent
-- name    : ValuationSubring.nonempty_fractionRing_tensorProduct_quotient_algEquiv_of_residueField_ringEquiv_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/4091fcfa-d477-5bac-bcd6-04306ac537c2
-- title:
--   Fraction field of k⊗_A V at a minimal prime is E'
-- statement:
--   Let $A$ be a commutative local ring, let $k$ be a field with an $A$-algebra structure killing the maximal ideal of $A$ (every $a\in\mathfrak m_A$ has $\mathrm{alg}_{A\to k}(a)=0$), and let $k$ also carry a structure of algebra over the residue field $\kappa=A/\mathfrak m_A$ compatible with it, in the sense that the image of the residue class of $a\in A$ in $k$ is the image of $a$. Let $K$ be a field with an $A$-algebra structure and $V\subseteq K$ a valuation subring containing the image of $A$, equipped with an $A$-algebra structure whose structure map is the one induced from $A\to K$. Assume $\mathfrak m_A=(\varpi)$ for an element $\varpi\in A$, and that every element of $K$ lying in the non-units of $V$ is the image of $\varpi$ times an element of $V$. Let $E$ be an intermediate field of $\kappa\subseteq\kappa((q))$ (Laurent series over $\kappa$) and $\theta:\kappa(V)\xrightarrow{\ \sim\ }E$ a ring isomorphism from the residue field of $V$ carrying the residue class of the image of $a\in A$ to the image of the residue class of $a$ under $\kappa\to E$. Assume that for every $n$ and every family $f:\mathrm{Fin}\,n\to\kappa((q))$ that is $\kappa$-linearly independent, the coefficientwise images of the $f_i$ under [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) applied to $\kappa\to k$ are $k$-linearly independent in $k((q))$. Let $E'$ be an intermediate field of $k\subseteq k((q))$ equal to the subfield generated over $k$ by the coefficientwise image of $E$. Then for every ideal $\mathfrak q$ of $k\otimes_A V$ that is a minimal prime of $k\otimes_A V$, there exists a $k$-algebra isomorphism $\operatorname{Frac}\big((k\otimes_A V)/\mathfrak q\big)\cong E'$.
--
--   This is the commutative-algebra core of the statement that base change of an unramified branch valuation ring along a constant field extension is computed on $q$-expansions: under the stated unramifiedness and linear disjointness hypotheses, $k\otimes_A V$ is identified with $k\otimes_\kappa\kappa(V)$ and embeds in $k((q))$, so its total fraction field at any minimal prime is the field generated over $k$ by the image of $E$. It is used in the identification of the function fields of the components of the geometric special fibre of a model of $X_1(Mp)$ with base changes of Igusa function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_nonempty_fractionRing_tensorProduct_quotient_algEquiv_of_residueField_ringEquiv_of_linearIndependent.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped TensorProduct

theorem ValuationSubring.nonempty_fractionRing_tensorProduct_quotient_algEquiv_of_residueField_ringEquiv_of_linearIndependent
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
    Nonempty (FractionRing (k ⊗[A] ↥V ⧸ 𝔮) ≃ₐ[k] ↥E') := by sorry
