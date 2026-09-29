-- Prove2me | Theorems.Thm_SPOBounds_StronglyConvex_normalCone_eq
-- name    : SPOBounds.StronglyConvex.normalCone_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:37:29.08957+00:00
-- url     : https://prove2.me/theorems/5b50c691-266a-40ea-9c99-dddf009fe555
-- title:
--   Proposition 1 (Vial 1983) — normal cones of $\bar\mu$-strongly convex sets
-- statement:
--   Let $E$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_*$, let $\bar\mu\ge0$, and let $S\subseteq E$ be a $\bar\mu$-strongly convex set. Then for every $\bar w\in S$ the normal cone of $S$ at $\bar w$ is
--   $$N_S(\bar w) = \Big\{c : c^\top(w-\bar w)\le -\Big(\frac{\bar\mu}{2}\Big)\|c\|_*\,\|w-\bar w\|^2 \text{ for all } w\in S\Big\}.$$
--
--   For $\bar\mu>0$ and $c\ne0$ this sharpens the defining inequality $c^\top(w-\bar w)\le0$ of the normal cone to a quadratic separation: $\bar w$ is the unique maximizer of $c^\top w$ over $S$, with a quadratic gap. It is the key geometric fact behind Theorem 7.
--
--   **Formalization Note** The statement is a set equality in `StrongDual ℝ E`. No compactness or non-singleton hypothesis is assumed, matching the proposition.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 23, Proposition 1, eq. (8) (proof: Appendix D.1, p. 35)

import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_StronglyConvex_StronglyConvexSet

namespace SPOBounds.StronglyConvex

/-- Proposition 1 (Vial 1983, Prop. 2.9), p. 23, eq. (8): for a `μ̄`-strongly convex set `S`
with `μ̄ ≥ 0` and any `w̄ ∈ S`,
`N_S(w̄) = {c : cᵀ(w − w̄) ≤ −(μ̄/2) ‖c‖_* ‖w − w̄‖² for all w ∈ S}`. -/
theorem normalCone_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {μbar : ℝ} (hμ : 0 ≤ μbar) {S : Set E}
    (hSsc : StronglyConvexSet μbar S) {wbar : E} (hwbar : wbar ∈ S) :
    normalCone S wbar =
      {c : StrongDual ℝ E | ∀ v ∈ S, c (v - wbar) ≤ -(μbar / 2) * ‖c‖ * ‖v - wbar‖ ^ 2} := by sorry

end SPOBounds.StronglyConvex
