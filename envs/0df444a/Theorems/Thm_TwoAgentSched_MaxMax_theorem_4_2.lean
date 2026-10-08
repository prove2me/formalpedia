-- Prove2me | Theorems.Thm_TwoAgentSched_MaxMax_theorem_4_2
-- name    : TwoAgentSched.MaxMax.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:14.411594+00:00
-- url     : https://prove2.me/theorems/13a513d9-f55e-4afb-80a4-884e6c83668d
-- title:
--   Theorem 4.2 — re-optimizing B under $f^A_{\max}\le Q_A$ gives a nondominated schedule
-- statement:
--   Let $n_A\ge1$, $n_B\ge1$, let the processing times be nonnegative and the cost functions nondecreasing, and fix a bound $Q$. Let $\sigma^*$ be an optimal schedule for $1\|f^A_{\max} : f^B_{\max}\le Q$ and put $Q_A=f^A_{\max}(\sigma^*)$. Exchange the roles of the agents and let $\tilde\sigma$ be an optimal schedule for
--   $$1\|f^B_{\max} : f^A_{\max}\le Q_A,$$
--   that is, $\tilde\sigma$ minimizes $f^B_{\max}$ among the schedules with $f^A_{\max}\le Q_A$. Then $\tilde\sigma$ is **nondominated**: no schedule $\sigma'$ has $f^A_{\max}(\sigma')\le f^A_{\max}(\tilde\sigma)$ and $f^B_{\max}(\sigma')\le f^B_{\max}(\tilde\sigma)$ with at least one inequality strict.
--
--   The result turns the single-criterion solution of §4 into a point of the Pareto frontier of the two agents with one further optimization, without the binary search over $Q$ described in §3.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 233, §4.1, Theorem 4.2 (σ̃ defined in the preceding paragraph)

import Mathlib
import Definitions.Def_TwoAgentSched_MaxMax_Model

namespace TwoAgentSched.MaxMax

/-- Theorem 4.2 (Agnetis et al. 2004, §4.1, p. 233). Let `σ*` be optimal for
`1‖f^A_max : f^B_max ≤ Q`, let `Q_A = f^A_max(σ*)`, and let `σ̃` be optimal for the problem with
the roles exchanged, `1‖f^B_max : f^A_max ≤ Q_A`. Then `σ̃` is nondominated for
`(f^A_max, f^B_max)`. -/
theorem theorem_4_2 {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB) (p : Job nA nB → ℝ)
    (hp : ∀ j, 0 ≤ p j) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (hfA : ∀ h, Monotone (fA h)) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (σstar σtilde : List (Job nA nB)) (hstar : IsOptimal hA p fA fB Q σstar)
    (htilde : IsOptimalSwap hB p fA fB (maxCostA hA p fA σstar) σtilde) :
    IsNondominated hA hB p fA fB σtilde := by sorry

end TwoAgentSched.MaxMax
