-- Prove2me | Theorems.Thm_TwoAgentSched_deadline_exists
-- name    : TwoAgentSched.deadline_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:51:41.490681+00:00
-- url     : https://prove2.me/theorems/c172c07e-bd7c-4886-854b-38d37c62b736
-- title:
--   p. 233: deadlines $D^B_k$ exist
-- statement:
--   Let $f$ be nondecreasing on $[0,\infty)$ and $Q$ a real number.
--
--   1. Some cut $D$ represents $f$ and $Q$:
--   $$
--   f(t) \le Q \iff (t,\mathrm{true}) \le D \qquad (t \ge 0).
--   $$
--   2. Whenever a real deadline $d$ in the paper's sense exists, i.e. $f(t)\le Q$ for $0\le t\le d$ and $f(t)>Q$ for $t>d$, the cut $(d,\mathrm{true})$ represents $f$ and $Q$.
--
--   The first part is what lets the algorithm work with a deadline for every B-job; the second shows that the cut is the paper's deadline whenever the latter exists.
--
--   Differences from the source:
--   - generalization: a real deadline D^B_k with f^B_k(C) ≤ Q for C ≤ D^B_k and f^B_k(C) > Q for C > D^B_k → a cut D k : WithTop (ℝ ×ₗ Bool) with f^B_k(t) ≤ Q ↔ (t, true) ≤ D k for t ≥ 0 (IsDeadline); reason: the paper's real deadline need not exist (f = 0 on [0, 1) and 1 after, Q = 0); when it exists, (D^B_k, true) is such a cut (deadline_exists), so the statement specializes to the paper's
--   - generalization: each f_i(·) a nondecreasing function of the completion time → each cost function MonotoneOn [0, ∞); reason: completion times are ≥ 0, so values at negative arguments never enter; every nondecreasing function is an instance
--   - generalization: an integer Q → Q : ℝ; reason: integers are reals; nothing in the argument uses integrality
--   - encoding: C^B_k ⩽ D^B_k and C^B_k > D^B_k for completion times C^B_k → the conditions for every real t ≥ 0; reason: completion times are exactly the nonnegative reals that can occur; the deadline's values below 0 are never used
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), p. 233 ("For each B-job J^B_k, let us define a deadline D^B_k, such that f^B_k(C^B_k) ⩽ Q for C^B_k ⩽ D^B_k and f^B_k(C^B_k) > Q for C^B_k > D^B_k")

import Mathlib
import Definitions.Def_TwoAgentSched_IsDeadline

namespace TwoAgentSched

/-- **Deadlines exist** (Agnetis–Mirchandani–Pacciarelli–Pacifici, Oper. Res. 52(2) (2004),
p. 233: "For each B-job `J^B_k`, let us define a deadline `D^B_k`, such that `f^B_k(C^B_k) ⩽ Q`
for `C^B_k ⩽ D^B_k` and `f^B_k(C^B_k) > Q` for `C^B_k > D^B_k`").
For every `f` nondecreasing on `[0, ∞)` and every `Q`:
1. some cut `D : WithTop (ℝ ×ₗ Bool)` represents `f` and `Q` (`IsDeadline f Q D`);
2. whenever a real deadline `d` in the paper's sense exists, the cut `(d, true)` represents
   `f` and `Q`. -/
theorem deadline_exists (f : ℝ → ℝ) (Q : ℝ) (hf : MonotoneOn f (Set.Ici 0)) :
    (∃ D : WithTop (ℝ ×ₗ Bool), IsDeadline f Q D) ∧
    ∀ d : ℝ, (∀ t, 0 ≤ t → t ≤ d → f t ≤ Q) → (∀ t, 0 ≤ t → d < t → Q < f t) →
      IsDeadline f Q ((toLex (d, true) : ℝ ×ₗ Bool) : WithTop (ℝ ×ₗ Bool)) := by sorry

end TwoAgentSched
