-- Prove2me | Theorems.Thm_WeierstrassProjModel_apply_schemeHomOverComp_eq_of_finite_of_forall_not_mem
-- name    : WeierstrassProjModel.apply_schemeHomOverComp_eq_of_finite_of_forall_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/6744fbf4-6950-50a5-8fa2-b3d2da114dd4
-- title:
--   Agreement off a finite set of points extends to all points
-- statement:
--   Let $k$ be an algebraically closed field and let $X$ be an elliptic Weierstrass curve over $k$, with projective model $E = \operatorname{Proj}$ of the graded quotient ring attached to `X.toProjective` and structure morphism $\pi =$ `projModelStrCR X.toProjective` to $\operatorname{Spec} k$. Assume given: a relative group law $G$ on $\pi$, that is, for every $k$-scheme $t : T \to \operatorname{Spec} k$ a multiplication, unit and inverse on the set of sections $\{\varphi : T \to E \mid \varphi \text{ followed by } \pi = t\}$, satisfying the group axioms and natural in $T$; a bijection $\mathrm{ev}$ from the sections over $\operatorname{Spec}$ of $\operatorname{id}_k$ (the $k$-points of $E$) to the group of points of the base change of $X$ to $k$, which by hypothesis carries $G$-multiplication of $k$-points to addition of points; an additive endomorphism $\alpha$ of that group of points; a morphism $\varphi : E \to E$ with $\varphi$ followed by $\pi$ equal to $\pi$; and a finite set $S$ of $k$-points of $E$ such that $\mathrm{ev}(P \text{ followed by } \varphi) = \alpha(\mathrm{ev}(P))$ for every $k$-point $P \notin S$. Then this equality holds for every $k$-point $P$ of $E$.
--
--   This is the rigidity step used to identify self-maps of the projective Weierstrass model with endomorphisms of the group of points: a self-map over $k$ which induces $\alpha$ on all but finitely many $k$-points induces it on all of them. It feeds into [`WeierstrassProjModel.exists_schemeHomOver_forall_apply_eq_of_isRationallyRepresented_of_isAlgClosed`](thm.html#WeierstrassProjModel.exists_schemeHomOver_forall_apply_eq_of_isRationallyRepresented_of_isAlgClosed), and the proof draws on the smoothness, properness and geometric integrality of the projective model together with the rigidity lemma for pointed morphisms of group schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_apply_schemeHomOverComp_eq_of_finite_of_forall_not_mem.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra
open WeierstrassProjModel

theorem WeierstrassProjModel.apply_schemeHomOverComp_eq_of_finite_of_forall_not_mem
    {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
    (X : WeierstrassCurve k) [X.IsElliptic]
    (G : WeierstrassProjModel.RelativeGroupLaw k (projModelStrCR X.toProjective))
    (ev : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) (projModelStrCR X.toProjective) ≃
      (X.toProjective.baseChange k).toAffine.Point)
    (hev_add : ∀ P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) (projModelStrCR X.toProjective),
      ev (G.mul (Spec.map (CommRingCat.ofHom (algebraMap k k))) P Q) = ev P + ev Q)
    (α : (X.baseChange k).toAffine.Point →+ (X.baseChange k).toAffine.Point)
    (φ : SchemeHomOver (projModelStrCR X.toProjective) (projModelStrCR X.toProjective))
    (S : Set (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) (projModelStrCR X.toProjective)))
    (hS : S.Finite)
    (hφ : ∀ P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) (projModelStrCR X.toProjective),
      P ∉ S → ev (NeronModelInfra.schemeHomOverComp P φ) = α (ev P)) :
    ∀ P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) (projModelStrCR X.toProjective),
      ev (NeronModelInfra.schemeHomOverComp P φ) = α (ev P) := by sorry
