-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_Supplement_projector_expansion_bounds
-- name    : StochApproxDyn.WeakAPT.Supplement.projector_expansion_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T19:16:23.644236+00:00
-- url     : https://prove2.me/theorems/d79ec03c-cdbf-4c05-a8a0-325fd7788076
-- title:
--   Lemma 9.4 — a lower expansion bound on Ker P transfers to Ker P̃ for a nearby projector, and the twisted operators differ by O(ε)
-- statement:
--   Let $P,\tilde P:\mathbb R^m\to\mathbb R^m$ be two projectors ($P^2=P$, $\tilde P^2=\tilde P$) and $A:\mathbb R^m\to\mathbb R^m$ a linear map; norms of linear maps are operator norms for the Euclidean norm. Assume there exist $\varepsilon,\alpha>0$ such that
--
--   1. $\|P-\tilde P\|\le\varepsilon$,
--   2. $\|Au\|\ge\alpha\|u\|$ for all $u\in\operatorname{Ker}P$.
--
--   Then
--
--   $$\|Av\|\ge\big(\alpha(1-\varepsilon)-\varepsilon\|A\|\big)\|v\|\quad\text{for all }v\in\operatorname{Ker}\tilde P,$$
--
--   $$\big\|\tilde PA(\mathrm{Id}-\tilde P)-PA(\mathrm{Id}-P)\big\|\le\varepsilon\|A\|\big(1+\|P\|+\|\tilde P\|\big).$$
--
--   In the proof of Lemma 9.3 this transfers the expansion of $D\Phi_T$ along the invariant unstable bundle to the smooth approximating bundle $\tilde E^u$.
--
--   Differences from the source: none.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), pp. 51–52, Lemma 9.4

import Mathlib

namespace StochApproxDyn.WeakAPT.Supplement

/-- Lemma 9.4 (Benaïm 1999, pp. 51–52). Let `P, P̃ : ℝ^m → ℝ^m` be two projectors
(`P² = P`, `P̃² = P̃`) and `A : ℝ^m → ℝ^m` a linear map, all with the operator norm of the
Euclidean norm. Assume there exist `ε, α > 0` such that (i) `‖P − P̃‖ ≤ ε` and
(ii) `‖A u‖ ≥ α ‖u‖` for all `u ∈ Ker P` (`P u = 0`). Then
(i) `‖A v‖ ≥ (α(1 − ε) − ε‖A‖)‖v‖` for all `v ∈ Ker P̃` (`P̃ v = 0`), and
(ii) `‖P̃ A (Id − P̃) − P A (Id − P)‖ ≤ ε‖A‖(1 + ‖P‖ + ‖P̃‖)`. -/
theorem projector_expansion_bounds {m : ℕ}
    (P Pt A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hP : IsIdempotentElem P) (hPt : IsIdempotentElem Pt) (ε α : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (h_i : ‖P - Pt‖ ≤ ε) (h_ii : ∀ u, P u = 0 → α * ‖u‖ ≤ ‖A u‖) :
    (∀ v, Pt v = 0 → (α * (1 - ε) - ε * ‖A‖) * ‖v‖ ≤ ‖A v‖) ∧
      ‖Pt * A * (1 - Pt) - P * A * (1 - P)‖ ≤ ε * ‖A‖ * (1 + ‖P‖ + ‖Pt‖) := by sorry

end StochApproxDyn.WeakAPT.Supplement
