-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_theorem_1
-- name    : RandomSizeStable.Stability.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:24.863308+00:00
-- url     : https://prove2.me/theorems/66d06b4d-2f46-4221-8fe4-d7e3856f22f2
-- title:
--   Theorem 1 — a randomized voting rule with distortion at most 2.13609
-- statement:
--   There exists one randomized voting rule family $R$ on every finite nonempty electorate and candidate set. Each $R(E)$ is an actual lottery determined only by the strict-ranking profile $E$. For every such profile, every consistent finite-valued pseudometric $d$, and every candidate $c$, it satisfies
--   $$\operatorname{SC}_d(R(E))\le\frac{213609}{100000}\operatorname{SC}_d(c),
--   \qquad\frac{213609}{100000}<2.1361.$$
--   The family is chosen before profiles or metrics are supplied. Distinct points may have distance zero, and a zero optimum is included. No certificate, stability-existence hypothesis, or numerical grid restriction is assumed.
--
--   This is the exact existential voting-rule theorem from the paper. Its construction can select a stable lottery for the single fixed law $D^\star$ independently of all hidden metrics; existence and the distortion guarantee remain proof obligations.
--
--   Differences from the source:
--   - encoding: a rule on every finite nonempty profile → one family on Fin n and Fin m for all positive n,m; reason: relabeling covers every finite instance; the rule receives rankings and returns normalized nonnegative masses before any metric is quantified
--   - encoding: metric distortion at most 213609/100000 with 0/0 = 1 and positive/0 = infinity → the cost inequality for every consistent pseudometric and every reference candidate; reason: the bound is at least one, so this is equivalent to Definition 1 including zero optimum; 2.1361 is the exact rational 21361/10000
-- source:
--   Nisarg Shah, Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission #1342 (October 2026), p. 15, Theorem 1 (also p. 4).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_VotingRule

set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion

namespace RandomSizeStable.Stability

/-- Theorem 1, pp.4 and 15: one ranking-only rule family, chosen before all
profiles and all hidden consistent pseudometrics. Zero optimum is retained. -/
theorem theorem_1 :
    ∃ R : VotingRule,
      (213609 / 100000 : ℝ) < (21361 / 10000 : ℝ) ∧
      ∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (E : Election (Fin n) (Fin m)),
        HasDistortionAtMost E (R n m hn hm E).val (213609 / 100000) := by sorry

end RandomSizeStable.Stability
