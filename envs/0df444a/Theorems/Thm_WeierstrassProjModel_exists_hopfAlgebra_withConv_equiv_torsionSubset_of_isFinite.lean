-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite
-- name    : WeierstrassProjModel.exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/949b0252-0961-5509-9db6-8fc38d12eeea
-- title:
--   Finite Hopf algebra representing the n-torsion of a relative group law
-- statement:
--   Let $K$ be a field, $W$ an elliptic Weierstrass curve over $K$ and $n$ a natural number. Let $G$ be a relative group law on the structure morphism $\mathrm{Proj}$ of the projective model `projModelStrCR W.toProjective` over $\operatorname{Spec} K$, that is, functorial multiplication, unit and inversion operations on the sets `SchemeHomOver` of sections over varying $K$-schemes, satisfying the group axioms and compatible with base change. Let $ev$ be a family, indexed by fields $F$ with a $K$-algebra structure, of bijections between sections over $\operatorname{Spec} F \to \operatorname{Spec} K$ of the projective model and the points of the affine model of $W$ base changed to $F$, and assume `IsPointsEval`: each $ev_F$ turns $G.\mathrm{mul}$ into addition of points and intertwines `galTwist` $\sigma$ with the map induced on points by $\sigma$, for every $\sigma \in \operatorname{Aut}_K(F)$. Assume finally that the structure morphism to $\operatorname{Spec} K$ of the kernel scheme $G.\mathrm{schemeKer}\ n$, the pullback of the multiplication-by-$n$ endomorphism of the projective model along the unit section, is finite. Then there exist a commutative ring $A$ with a $K$-Hopf algebra structure such that $A$ is finite as a $K$-module and its comultiplication is cocommutative, together with a bijection $e_H$ from the convolution monoid `WithConv` $(A \to_{\mathrm{alg}[K]} \overline{K})$ of $K$-algebra maps $A \to \overline{K}$ onto the subtype of sections over $\operatorname{Spec}\overline{K}$ that are $n$-torsion for $G$ (those $x$ with $G.\mathrm{nsmul}\ n\ x$ equal to the unit section), such that: the underlying section of $e_H(f g)$ equals $G.\mathrm{mul}$ applied to the underlying sections of $e_H f$ and $e_H g$; and whenever $\sigma$ is a $K$-algebra automorphism of $\overline{K}$ and $g = \sigma \circ f$ pointwise on $A$, the underlying section of $e_H g$ equals `galTwist` $\sigma$ applied to that of $e_H f$.
--
--   This is the passage from the $n$-torsion subfunctor of the relative group law on a Weierstrass projective model to an honest finite flat commutative group scheme over $K$, presented Hopf-algebraically: the torsion points over $\overline{K}$ are identified, multiplicatively and Galois-equivariantly, with the $\overline{K}$-algebra characters of a finite cocommutative $K$-Hopf algebra. It is used by [`WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_relativeGroupLaw_isPointsEval`](thm.html#WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_relativeGroupLaw_isPointsEval), and ultimately supplies the Galois module $E[n]$ underlying the mod-$\ell$ representation attached to a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassProjModel.exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite
    (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ)
    (G : RelativeGroupLaw K (projModelStrCR W.toProjective))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F)))
          (projModelStrCR W.toProjective) ≃
        (W.toProjective.baseChange F).toAffine.Point)
    (hev : IsPointsEval W.toProjective G ev)
    (hfin : IsFinite (G.schemeKerStr n)) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eH : WithConv (A →ₐ[K] AlgebraicClosure K) ≃
            ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom
              (algebraMap K (AlgebraicClosure K)))) n),
        (∀ f g, (eH (f * g)).1 =
          G.mul (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
            (eH f).1 (eH g).1) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) → (eH g).1 = galTwist σ (eH f).1 := by sorry
