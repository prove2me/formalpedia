-- Prove2me | Theorems.Thm_TwoAgentSched_largest_deadline
-- name    : TwoAgentSched.largest_deadline
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:52:16.144442+00:00
-- url     : https://prove2.me/theorems/6ad50392-15b6-4a27-8dce-08ed26eb9ea9
-- title:
--   p. 233: only the B-job with the largest deadline needs to be considered
-- statement:
--   Let the deadlines $D^B_k$ (cuts) represent the functions $f^B_k$ and the bound $Q$. Let $U$ be a set of B-jobs, $k^*\in U$ one with the largest deadline in $U$, and $\bar\tau\ge0$. Then
--   $$
--   \exists\, k\in U:\ f^B_k(\bar\tau)\le Q \quad\iff\quad f^B_{k^*}(\bar\tau) \le Q .
--   $$
--
--   Hence, at each step of the algorithm, the only B-job that needs to be considered is the unscheduled one with the largest deadline.
--
--   Differences from the source:
--   - generalization: a real deadline D^B_k with f^B_k(C) ≤ Q for C ≤ D^B_k and f^B_k(C) > Q for C > D^B_k → a cut D k : WithTop (ℝ ×ₗ Bool) with f^B_k(t) ≤ Q ↔ (t, true) ≤ D k for t ≥ 0 (IsDeadline); reason: the paper's real deadline need not exist (f = 0 on [0, 1) and 1 after, Q = 0); when it exists, (D^B_k, true) is such a cut (deadline_exists), so the statement specializes to the paper's
--   - generalization: regular f^B_k → no monotonicity assumption on f^B_k; reason: only the representing property of the deadlines is used; regular functions are an instance
--   - generalization: an integer Q → Q : ℝ; reason: integers are reals; nothing in the argument uses integrality
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), p. 233 ("At each step the only B-job that needs to be considered is the unscheduled one with largest D^B_k")

import Mathlib
import Definitions.Def_TwoAgentSched_IsDeadline

namespace TwoAgentSched

/-- **Only the largest deadline matters** (Agnetis–Mirchandani–Pacciarelli–Pacifici, Oper. Res.
52(2) (2004), p. 233: "At each step the only B-job that needs to be considered is the
unscheduled one with largest `D^B_k`"). Let the deadlines `D k` represent `f^B_k` and `Q`, let
`U` be a set of B-jobs and `k* ∈ U` one with the largest deadline in `U`, and `τ̄ ≥ 0`. Then some
`k ∈ U` has `f^B_k(τ̄) ≤ Q` if and only if `f^B_{k*}(τ̄) ≤ Q`. -/
theorem largest_deadline {nB : ℕ} (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (D : Fin nB → WithTop (ℝ ×ₗ Bool)) (hD : ∀ k, IsDeadline (fB k) Q (D k))
    (U : Finset (Fin nB)) (kstar : Fin nB) (hk : kstar ∈ U) (hmax : ∀ k ∈ U, D k ≤ D kstar)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    (∃ k ∈ U, fB k τ ≤ Q) ↔ fB kstar τ ≤ Q := by sorry

end TwoAgentSched
