-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Transient_corollary_4_every
-- name    : VeinottSensitiveDP.Transient.corollary_4_every
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:51.640339+00:00
-- url     : https://prove2.me/theorems/4d6f1285-b59a-4491-8c8e-26841aa6c0bd
-- title:
--   Corollary 4 ("every") — every stationary ⇔ every periodic ⇔ every policy transient ⇔ ∃N ≧ 1, ‖Pᴺ(π)‖ < 1 ∀π; ⇔ ‖P^S(π)‖ < 1 ∀π if ‖P(g)‖ ≦ 1
-- statement:
--   In the dynamic program of §2 of Veinott (1969), with nonnegative transition weights and no row-sum bound, the following four statements are equivalent:
--
--   1. every stationary policy is transient;
--   2. every periodic policy is transient;
--   3. every policy is transient;
--   4. there is $N\ge 1$ such that $\|P^N(\pi)\|<1$ for every policy $\pi$.
--
--   If in addition $\|P(g)\|\le 1$ for all $g\in F$, they are also equivalent to
--
--   5. $\|P^S(\pi)\|<1$ for every policy $\pi$, where $S$ is the number of states.
--
--   Here $\|\cdot\|$ is the maximum absolute row sum. In 4 the same $N$ serves every policy. The corollary turns a condition on the finitely many stationary policies into transience of every policy, which is what makes the total reward of an arbitrary policy well defined in the rest of §2.
--
--   **Formalization Note.** Statements 1–4 are a `List.TFAE`; statement 5 is stated as equivalent to 1 under the extra hypothesis. $S$ is `Fintype.card St`.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1639, Corollary 4 (reading with "every")

import Mathlib
import Definitions.Def_VeinottSensitiveDP_Transient_Model

namespace VeinottSensitiveDP.Transient

open Matrix

variable {St : Type} [Fintype St] [DecidableEq St] [Nonempty St] {A : St → Type}
  [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]

/-- **Corollary 4**, reading with "every" (Veinott, *Discrete Dynamic Programming with Sensitive Discount Optimality Criteria*,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1639).
The following four statements are equivalent.
1°. Every stationary policy is transient.
2°. Every periodic policy is transient.
3°. Every policy is transient.
4°. For some `N ≧ 1`, `‖Pᴺ(π)‖ < 1` for every `π`.
If also `‖P(g)‖ ≦ 1` for all `g ∈ F`, the above are equivalent to
5°. `‖P^S(π)‖ < 1` for every `π`.

**Formalization Note.** `S` is the number of states, `Fintype.card St`. `‖·‖` is the maximum
absolute row sum. In 4° the `N` is chosen before `π` (one `N` for all policies). 5° is stated
as equivalent to 1°, which with the first part gives the equivalence with all of 1°–4°. -/
theorem corollary_4_every (D : Program St A) :
    List.TFAE
      [∀ f : DecisionRule St A, D.IsTransient (stationary f),
       ∀ π : Policy St A, IsPeriodic π → D.IsTransient π,
       ∀ π : Policy St A, D.IsTransient π,
       ∃ N : ℕ, 1 ≤ N ∧ ∀ π : Policy St A, rowSumNorm (D.PN N π) < 1] ∧
    ((∀ g : DecisionRule St A, rowSumNorm (D.Pmat g) ≤ 1) →
      ((∀ f : DecisionRule St A, D.IsTransient (stationary f)) ↔
        ∀ π : Policy St A, rowSumNorm (D.PN (Fintype.card St) π) < 1)) := by sorry

end VeinottSensitiveDP.Transient
