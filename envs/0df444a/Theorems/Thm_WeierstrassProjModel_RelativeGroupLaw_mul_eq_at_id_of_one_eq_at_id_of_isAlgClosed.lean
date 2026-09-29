-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed
-- name    : WeierstrassProjModel.RelativeGroupLaw.mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/beaff82d-fec1-5287-9f1f-e0029792eb9f
-- title:
--   Rigidity: equal units at id force equal multiplications on K-points
-- statement:
--   Let $K$ be an algebraically closed field and let $x\colon X \to \operatorname{Spec} K$ be a morphism of schemes which is proper, with $X$ integral and the fibre product $X \times_{\operatorname{Spec} K} X$ (the categorical pullback of $x$ with itself) reduced. Let $G_1, G_2$ be two relative group laws on $x$ over $K$, that is, two structures assigning to each scheme $T$ and each morphism $t\colon T \to \operatorname{Spec} K$ a multiplication, a unit element and an inversion on the set $\{\varphi\colon T \to X \mid \varphi \text{ followed by } x = t\}$ of $T$-points of $X$ over $t$, subject to associativity, the two unit laws, left inverses, and naturality of the multiplication under precomposition with any $\psi\colon T' \to T$ satisfying $\psi$ followed by $t$ equals $t'$. Assume the two unit elements attached to the identity test morphism $\mathbf{1}_{\operatorname{Spec} K}$ coincide. Then for all $P, Q$ in the set of morphisms $\operatorname{Spec} K \to X$ over $\mathbf{1}_{\operatorname{Spec} K}$, i.e. all $K$-sections of $x$, the two multiplications agree: $G_1.\mathrm{mul}(\mathbf{1})(P,Q) = G_2.\mathrm{mul}(\mathbf{1})(P,Q)$. The conclusion is asserted only at the identity test morphism, not for general $T$.
--
--   This is the corollary of Mumford's rigidity lemma — a group law on a proper integral variety is determined by its identity element — transcribed for the project's notion of a relative group law on a scheme over $\operatorname{Spec} K$, at the level of $K$-points. It feeds the statement [`WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isAlgClosed`](thm.html#WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isAlgClosed), where the agreement of the two multiplications is propagated from $K$-points to arbitrary test schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
  GoodReductionJacobian WeierstrassProjModel

universe u

theorem WeierstrassProjModel.RelativeGroupLaw.mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) [IsProper x] [IsIntegral X]
    [IsReduced ↑(pullback x x)]
    (G₁ G₂ : WeierstrassProjModel.RelativeGroupLaw K x)
    (h : G₁.one (𝟙 _) = G₂.one (𝟙 _)) :
    ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) x,
      G₁.mul (𝟙 _) P Q = G₂.mul (𝟙 _) P Q := by sorry
