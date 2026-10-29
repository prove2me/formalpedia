-- Prove2me | Theorems.Thm_PutermanMDP_Sensitive_finite_sensitivity_blackwell
-- name    : PutermanMDP.Sensitive.finite_sensitivity_blackwell
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:09.026191+00:00
-- url     : https://prove2.me/theorems/08755f3f-9d0c-4a07-8af2-bd46520f2ac4
-- title:
--   Theorem 10.3.6 — finite sensitivity implies Blackwell optimality
-- statement:
--   Consider a finite-state, finite-action Markov decision process, and let $d^*$ be a deterministic stationary decision rule. Suppose $P_{d^*}$ has $r$ recurrent classes and $(d^*)^\infty$ is $(|S|-r-1)$-discount optimal. The printed theorem asserts both conclusions:
--   $$(d^*)^\infty\text{ is Blackwell optimal},$$
--   $$\forall n\in\mathbb Z,\ n\ge-1\ \Longrightarrow\ (d^*)^\infty\text{ is }n\text{-discount optimal}.$$
--   All optimality comparisons are against every history-dependent randomized policy. This policy-specific threshold is the mission's faithful goal. FINDINGS records an explicit two-state counterexample to the printed theorem; no corrected claim is substituted.
--
--   **Formalization Note** $r$ counts the closed irreducible classes of $P_{d^*}$ itself, not a minimum over other policies. The threshold is computed in the integers, including $-1$.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 518 (PDF 534), Theorem 10.3.6; https://doi.org/10.1002/9780470316887

import Mathlib
import Definitions.Def_PutermanMDP_Sensitive_Model

namespace PutermanMDP.Sensitive

/-- Printed Theorem 10.3.6; its policy-specific recurrent count is preserved. -/
theorem finite_sensitivity_blackwell {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    (M : Model S A) (dstar : DecisionRule M) (r : ℕ)
    (hopt : NDiscountOptimal (stationary dstar) ((Fintype.card S : ℤ) - (r : ℤ) - 1))
    (hr : recurrentCount (policyMatrix dstar) = r) :
    BlackwellOptimal (stationary dstar) ∧
      ∀ n : ℤ, -1 ≤ n → NDiscountOptimal (stationary dstar) n := by sorry

end PutermanMDP.Sensitive
