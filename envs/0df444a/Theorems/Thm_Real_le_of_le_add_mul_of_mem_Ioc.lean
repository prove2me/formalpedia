-- Prove2me | Theorems.Thm_Real_le_of_le_add_mul_of_mem_Ioc
-- name    : Real.le_of_le_add_mul_of_mem_Ioc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T04:18:39.587436+00:00
-- url     : https://prove2.me/theorems/a631c8bb-ef17-4c11-93a6-fd8433092ef4
-- title:
--   Letting the slack go to zero in $A \le B + tC$
-- statement:
--   Let $A$, $B$ and $C$ be real numbers and suppose
--
--   $$
--   A \;\le\; B + t\,C \qquad \text{for every } t \in (0, 1].
--   $$
--
--   Then $A \le B$.
--
--   The slack $tC$ can be sent to zero even though $t = 0$ is excluded from the hypothesis, and no
--   sign condition on $C$ is needed. This is the step at the end of a great many convergence
--   proofs: a one-step inequality is established for every small positive step size, and the
--   conclusion wanted is the inequality at step size zero. Stated separately it saves repeating the
--   same `le_of_forall_lt`-style argument, and it is needed exactly where a `Filter.Tendsto`
--   argument would be heavier than the fact deserves.
-- source:
--   Elementary limiting argument. Carved from the accepted proof of NesterovFB.Weak.theorem_3 (the rate of convergence of Nesterov’s accelerated forward-backward method), https://prove2.me/submissions/e3454a9c-3502-4c6b-9794-7eebefc4332c

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_NesterovFB_Weak_Algorithm

open Filter Topology NNReal
open InnerProductSpace
open ThreeOpSplitting.ConvexRates

theorem Real.le_of_le_add_mul_of_mem_Ioc {A B C : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≤ B + t * C) : A ≤ B := by sorry
