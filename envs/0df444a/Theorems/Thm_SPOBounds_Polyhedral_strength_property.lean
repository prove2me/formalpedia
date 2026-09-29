-- Prove2me | Theorems.Thm_SPOBounds_Polyhedral_strength_property
-- name    : SPOBounds.Polyhedral.strength_property
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:48:16.164736+00:00
-- url     : https://prove2.me/theorems/4c00b667-15e1-4e88-8ee7-40409eac1eab
-- title:
--   Theorem 8 — polytopes satisfy the strength property with $\mu=2/\Delta(S)$
-- statement:
--   Let $E$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_*$, let $v_1,\dots,v_K\in E$ be pairwise distinct, and let $S=\mathrm{conv}\{v_1,\dots,v_K\}$ be not a singleton, with diameter $\Delta(S)=\sup_{w_1,w_2\in S}\|w_1-w_2\|$. Let $w^*$ be any optimization oracle for $S$. Then $S$ satisfies the strength property with parameter $\mu=2/\Delta(S)>0$:
--   $$\hat c^\top\big(w-w^*(\hat c)\big)\ \ge\ \frac{\nu_S(\hat c)}{\Delta(S)}\,\|w-w^*(\hat c)\|^2\qquad\text{for all } w\in S\text{ and all cost vectors }\hat c,$$
--   where $\nu_S$ is the distance to degeneracy.
--
--   Together with the margin-based generalization bounds of the paper (Theorems 4 and 5), this gives generalization guarantees for the SPO loss over any polytope with a known convex hull representation, such as the unit simplex of multiclass classification.
--
--   **Formalization Note** The conclusion states $2/\Delta(S)>0$ explicitly, since Definition 3 requires a positive parameter; $\Delta(S)$ is `Metric.diam S`, which is the true diameter here because $S$ is bounded, and is positive because $S$ is not a singleton. The strength predicate is the one of Definition 3 with $\mu\,\nu_S(\hat c)/2$ for $\mu=2/\Delta(S)$. The polytope is given by pairwise distinct points `v : Fin K → E` with $S=$ `convexHull ℝ (Set.range v)`; non-emptiness, compactness and convexity follow from that representation.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 25, Theorem 8 (strength claim; proof pp. 25–26)

import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy

namespace SPOBounds.Polyhedral

/-- Theorem 8, strength claim, arXiv:1905.11488v3, p. 25: if `S = conv{v_1, …, v_K}` (distinct
`v_i`) is not a singleton, then for every optimization oracle `w*` the strength property (5)
holds with parameter `μ = 2 / Δ(S)`, where `Δ(S)` is the diameter of `S`; the parameter is
positive, as Definition 3 requires. -/
theorem strength_property {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : ℕ} (v : Fin K → E) (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : ∀ c : StrongDual ℝ E, w c ∈ S ∧ ∀ x ∈ S, c (w c) ≤ c x) :
    0 < 2 / Metric.diam S ∧ SPOBounds.Shared.StrengthProperty S (2 / Metric.diam S) w := by sorry

end SPOBounds.Polyhedral
