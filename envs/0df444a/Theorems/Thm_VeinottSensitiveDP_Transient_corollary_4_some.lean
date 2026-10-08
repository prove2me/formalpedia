-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Transient_corollary_4_some
-- name    : VeinottSensitiveDP.Transient.corollary_4_some
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:45.070523+00:00
-- url     : https://prove2.me/theorems/470eb2b2-fd17-4031-aeb4-1f3ee6d04f15
-- title:
--   Corollary 4 ("some") — some stationary ⇔ some periodic ⇔ some policy transient ⇔ ∃N ≧ 1, π with ‖Pᴺ(π)‖ < 1; ⇔ ∃π, ‖P^S(π)‖ < 1 if ‖P(g)‖ ≦ 1
-- statement:
--   In the dynamic program of §2 of Veinott (1969), with nonnegative transition weights and no row-sum bound, the following four statements are equivalent:
--
--   1. some stationary policy is transient;
--   2. some periodic policy is transient;
--   3. some policy is transient;
--   4. there are $N\ge 1$ and a policy $\pi$ with $\|P^N(\pi)\|<1$.
--
--   If in addition $\|P(g)\|\le 1$ for all $g\in F$, they are also equivalent to
--
--   5. $\|P^S(\pi)\|<1$ for some policy $\pi$, where $S$ is the number of states.
--
--   Here $\|\cdot\|$ is the maximum absolute row sum. The equivalence of 1 and 3 was shown by Derman for substochastic transition matrices; this corollary removes that hypothesis.
--
--   **Formalization Note.** Statements 1–4 are a `List.TFAE`; statement 5 is stated as equivalent to 1 under the extra hypothesis. $S$ is `Fintype.card St`.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1639, Corollary 4 (reading with "some")

import Mathlib
import Definitions.Def_VeinottSensitiveDP_Transient_Model

namespace VeinottSensitiveDP.Transient

open Matrix

variable {St : Type} [Fintype St] [DecidableEq St] [Nonempty St] {A : St → Type}
  [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]

/-- **Corollary 4**, reading with "some" (Veinott, *Discrete Dynamic Programming with Sensitive Discount Optimality Criteria*,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1639).
The following four statements are equivalent.
1°. Some stationary policy is transient.
2°. Some periodic policy is transient.
3°. Some policy is transient.
4°. For some `N ≧ 1`, `‖Pᴺ(π)‖ < 1` for some `π`.
If also `‖P(g)‖ ≦ 1` for all `g ∈ F`, the above are equivalent to
5°. `‖P^S(π)‖ < 1` for some `π`.

**Formalization Note.** `S` is the number of states, `Fintype.card St`. `‖·‖` is the maximum
absolute row sum. No row-sum bound is assumed for 1°–4°. -/
theorem corollary_4_some (D : Program St A) :
    List.TFAE
      [∃ f : DecisionRule St A, D.IsTransient (stationary f),
       ∃ π : Policy St A, IsPeriodic π ∧ D.IsTransient π,
       ∃ π : Policy St A, D.IsTransient π,
       ∃ N : ℕ, 1 ≤ N ∧ ∃ π : Policy St A, rowSumNorm (D.PN N π) < 1] ∧
    ((∀ g : DecisionRule St A, rowSumNorm (D.Pmat g) ≤ 1) →
      ((∃ f : DecisionRule St A, D.IsTransient (stationary f)) ↔
        ∃ π : Policy St A, rowSumNorm (D.PN (Fintype.card St) π) < 1)) := by sorry

end VeinottSensitiveDP.Transient
