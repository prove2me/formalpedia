-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_eq_one_of_forall_nsmul_eq_zero
-- name    : WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.eq_one_of_forall_nsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/9937a1cf-1e59-5a85-b3a6-bb040ceeb919
-- title:
--   Drinfeld Γ(q)-bases are trivial without rational q-torsion
-- statement:
--   Let $K$ be a field and $W$ a Weierstrass cubic in projective form over $K$ whose discriminant $W.\Delta$ is a unit. Let $G$ be a relative group law on the projective plane model $E = \mathrm{Proj}$ of $W$ over $\operatorname{Spec} K$, that is, a functorial group structure (multiplication, unit, inverse, the group axioms and naturality under base change) on the sets $\{\varphi : T \to E \mid \varphi \text{ followed by the structure morphism } = t\}$ of sections over arbitrary $t : T \to \operatorname{Spec} K$. Let $ev$ be a family, indexed by fields $F$ equipped with a $K$-algebra structure, of bijections from the set of sections of $E$ over $\operatorname{Spec}$ of $K \to F$ to the affine points $(W \times_K F)(F)$, and assume `IsPointsEval W G ev`: each $ev_F$ carries $G$-multiplication to addition of points and commutes with the action of $\mathrm{Aut}_K(F)$ on both sides. Let $q$ be a prime and assume that $W$ has no nonzero $K$-rational $q$-torsion, i.e. $q \cdot R = 0$ implies $R = 0$ for every affine point $R$ of $W$ over $K$. Then for any two sections $P, Q$ of $E$ over the identity of $\operatorname{Spec} K$ satisfying `IsDrinfeldBasis G q P Q` — the equality, as ideal sheaf data on the pullback of $E$ along the identity, of the product-of-kernel-graphs ideal of the tuple $(aP+bQ)$ attached to $G, q, P, Q$ with the kernel ideal of the $q$-torsion subscheme, i.e. of the first projection of the pullback of the $q$-multiplication morphism against the unit section followed by `toPullbackId` — one has $P =$ the unit section and $Q =$ the unit section.
--
--   This is the uniqueness half of the statement that, over a field with no rational $q$-torsion on $W$ (for $K$ algebraically closed of characteristic $q$, exactly the supersingular case), the Drinfeld $\Gamma(q)$-level structure slot in the sense of Katz–Mazur has only the trivial basis $(O,O)$. It is used in the study of the supersingular points of the modular curve of full level $q$ and of the diamond/level automorphisms acting there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_eq_one_of_forall_nsmul_eq_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.eq_one_of_forall_nsmul_eq_zero
    {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve.Projective K) (hΔ : IsUnit W.Δ)
    (G : RelativeGroupLaw K (projModelStrCR W))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR W) ≃ (W.baseChange F).toAffine.Point)
    (hev : IsPointsEval W G ev)
    (q : ℕ) [Fact q.Prime]

    (hss : ∀ R : W.toAffine.Point, q • R = 0 → R = 0)
    (P Q : Section W) (hPQ : IsDrinfeldBasis G q P Q) :
    P = G.one (𝟙 _) ∧ Q = G.one (𝟙 _) := by sorry
