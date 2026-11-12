-- Prove2me | Theorems.Thm_RobotMP_W1Hard_lemma_9_9
-- name    : RobotMP.W1Hard.lemma_9_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:42:35.234694+00:00
-- url     : https://prove2.me/theorems/8b179286-635e-4199-abe6-f91113509ce2
-- title:
--   Lemma 9.9 — reachable balanced configurations keep z = n·x + y
-- statement:
--   Consider the synchronizer together with the odometer, with parameter $n$. Suppose $b$ is reachable from $a$, where $a$ has $(x_1, x_2, x_3) = (i, i, i)$, $(y_1, y_2, y_3) = (j, j, j)$, $(z_1, z_2, z_3) = (ni + j, ni + j, ni + j)$, and $b$ has $(x_1, x_2, x_3) = (i', i', i')$, $(y_1, y_2, y_3) = (j', j', j')$ and $z_1 = z_2 = z_3$. Then in $b$
--   $$z_1 = z_2 = z_3 = n i' + j'.$$
--
--   This invariant is what makes the tester's constraint on $z_1$ a constraint on $(x_1, y_1)$.
--
--   Differences from the source:
--   - reading: the constraint lists of pp. 47 and 50 → imposed directly in the extended syntax of p. 44; the constants n − 1, n, 0 appear directly instead of three fixed data variables; reason: the paper reasons about the extended constraints themselves.
--   - reading: the printed odometer constraint "{x1 − x3} ∈ {0, 1}" → x1 − x3 ∈ {0, 1}; reason: obvious typo.
-- source:
--   Agarwal, Holmgren, Stade, Near-Optimal Makespan and Parameterized Hardness for Multi-Robot Motion Planning, STOC 2027 submission (manuscript sha256 17b4fe59…), p. 51, Lemma 9.9

import Mathlib
import Definitions.Def_RobotMP_W1Hard_Gadgets

set_option autoImplicit false

namespace RobotMP.W1Hard

/-- Lemma 9.9: in the synchronizer–odometer system, a reconfiguration from
`x = (i, i, i)`, `y = (j, j, j)`, `z = (ni + j, ni + j, ni + j)` to a configuration with
`x = (i', i', i')`, `y = (j', j', j')` and `z₁ = z₂ = z₃` ends with `z₁ = z₂ = z₃ = ni' + j'`. -/
theorem lemma_9_9 (n : ℕ) (a b : GConfig OdoData OdoCtrl) (i j i' j' : ℤ)
    (hreach : GReach (SyncOdoSystem n) a b)
    (ha : a.1 .x1 = i ∧ a.1 .x2 = i ∧ a.1 .x3 = i ∧ a.1 .y1 = j ∧ a.1 .y2 = j ∧ a.1 .y3 = j ∧
      a.1 .z1 = n * i + j ∧ a.1 .z2 = n * i + j ∧ a.1 .z3 = n * i + j)
    (hb : b.1 .x1 = i' ∧ b.1 .x2 = i' ∧ b.1 .x3 = i' ∧ b.1 .y1 = j' ∧ b.1 .y2 = j' ∧
      b.1 .y3 = j' ∧ b.1 .z1 = b.1 .z2 ∧ b.1 .z2 = b.1 .z3) :
    b.1 .z1 = n * i' + j' ∧ b.1 .z2 = n * i' + j' ∧ b.1 .z3 = n * i' + j' := by sorry

end RobotMP.W1Hard
