-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_relativeGroupLaw_isPointsEval
-- name    : WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_relativeGroupLaw_isPointsEval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/99690b83-0ffb-5905-9573-121d0bb1f422
-- title:
--   Torsion Hopf algebra of W[n] over a field
-- statement:
--   Let $K$ be a field, let $W$ be a Weierstrass curve over $K$ which is elliptic, and let $n$ be a prime. Three inputs for the projective model of $W$ are assumed: (i) `hbc`, that for every field $L$ with a $K$-algebra structure the pullback of the structure morphism `projModelStrCR W.toProjective` (from $\mathrm{Proj}$ of the graded quotient ring of the projective model down to $\operatorname{Spec} K$) along $\operatorname{Spec}(K\to L)$ is isomorphic as a scheme to `projModelCR` of the base change of `W.toProjective` to $L$; (ii) a relative group law $G$ on that structure morphism, i.e. for every scheme $T$ with a morphism $t$ to $\operatorname{Spec} K$ a multiplication, unit and inverse on the set of morphisms $\varphi$ from $T$ to the projective model with $\varphi$ followed by the structure morphism equal to $t$, satisfying associativity, the unit laws and left inverse, and compatible with composition along any $\psi : T' \to T$ over $\operatorname{Spec} K$; (iii) for every field $F$ with a $K$-algebra structure an equivalence $\mathrm{ev}_F$ between those $F$-points over $\operatorname{Spec}(K\to F)$ and the affine points of the base change of `W.toProjective` to $F$, together with `hev`, the assertion that $\mathrm{ev}_F$ carries the multiplication of $G$ to addition of points and carries the twist of a point by $\sigma \in \mathrm{Aut}_K(F)$ (composition with $\operatorname{Spec}\sigma$) to the map induced by $\sigma$ on points. The conclusion, with classical decidable equality on $\overline{K} =$ `AlgebraicClosure K`, is the existence of a type $A$ with a commutative ring structure and a $K$-Hopf algebra structure such that $A$ is finite as a $K$-module and its comultiplication is cocommutative, together with an equivalence $e_A$ from the $K$-algebra homomorphisms $A \to \overline{K}$, equipped with the convolution product (`WithConv`), to the $\mathbb{Z}$-torsion submodule killed by $n$ of the group of points of $W$ base changed to $\overline{K}$, such that $e_A(fg) = e_A f + e_A g$ for all $f, g$, and such that whenever $\sigma \in \mathrm{Aut}_K(\overline K)$ and $g a = \sigma(f a)$ for all $a \in A$, one has $e_A g = \sigma \bullet e_A f$.
--
--   This realises the $n$-torsion subscheme $W[n]$ of an elliptic curve over a field as a finite cocommutative Hopf algebra $A$ over $K$, with a Galois-equivariant identification of $\operatorname{Hom}_{K\text{-alg}}(A,\overline K)$ with $W[n](\overline K)$; it is the passage from the scheme-theoretic group law on the projective model to the algebraic data underlying the mod $n$ Galois representation. It is cited in the specialisations of the construction over $\mathbb{Q}$ and over $p$-adic fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_relativeGroupLaw_isPointsEval.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_relativeGroupLaw_isPointsEval
    (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ) [Fact n.Prime]
    (hbc : ∀ (L : Type) [Field L] [Algebra K L],
        Nonempty (pullback (projModelStrCR W.toProjective)
            (Spec.map (CommRingCat.ofHom (algebraMap K L)))
          ≅ projModelCR (W.toProjective.baseChange L)))
    (G : RelativeGroupLaw K (projModelStrCR W.toProjective))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F)))
          (projModelStrCR W.toProjective) ≃
        (W.toProjective.baseChange F).toAffine.Point)
    (hev : IsPointsEval W.toProjective G ev) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eA : WithConv (A →ₐ[K] AlgebraicClosure K) ≃
            Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f) := by sorry
