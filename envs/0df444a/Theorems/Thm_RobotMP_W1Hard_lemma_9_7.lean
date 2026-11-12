-- Prove2me | Theorems.Thm_RobotMP_W1Hard_lemma_9_7
-- name    : RobotMP.W1Hard.lemma_9_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:42:29.785041+00:00
-- url     : https://prove2.me/theorems/14811dfa-24de-4b1b-8689-46f601dc0e35
-- title:
--   Lemma 9.7 — while q = 0, the synchronizer preserves i − j
-- statement:
--   In the synchronizer constraint system with parameter $n$, suppose $b$ is reachable from $a$ by moves through configurations with $q = 0$, where $a$ has $(y_1, y_2, y_3) = (i, i, i)$, $(z_1, z_2, z_3) = (j, j, j)$ and $b$ has $(y_1, y_2, y_3) = (i', i', i')$, $(z_1, z_2, z_3) = (j', j', j')$. Then
--   $$i - j = i' - j'.$$
--
--   This is the invariant half of the synchronizer: with $q = 0$ the $y$- and $z$-blocks can only move together.
--
--   Differences from the source:
--   - reading: the synchronizer's constraint list of p. 47 → imposed directly in the extended syntax of p. 44, without the auxiliary variables that simulate it; reason: the paper reasons about the extended constraints themselves.
--   - reading: "while keeping q = 0" → q = 0 at every configuration of the reconfiguration (c is free); reason: the paper's meaning of keeping a variable fixed.
-- source:
--   Agarwal, Holmgren, Stade, Near-Optimal Makespan and Parameterized Hardness for Multi-Robot Motion Planning, STOC 2027 submission (manuscript sha256 17b4fe59…), p. 49, Lemma 9.7

import Mathlib
import Definitions.Def_RobotMP_W1Hard_Gadgets

set_option autoImplicit false

namespace RobotMP.W1Hard

/-- Lemma 9.7: a synchronizer reconfiguration that keeps `q = 0` between balanced
configurations preserves `i − j`. -/
theorem lemma_9_7 (n : ℕ) (a b : GConfig SyncData SyncCtrl) (i j i' j' : ℤ)
    (hreach : GReach (fun s => SyncSystem n s ∧ s.2 .q = false) a b)
    (ha : a.1 .y1 = i ∧ a.1 .y2 = i ∧ a.1 .y3 = i ∧ a.1 .z1 = j ∧ a.1 .z2 = j ∧ a.1 .z3 = j)
    (hb : b.1 .y1 = i' ∧ b.1 .y2 = i' ∧ b.1 .y3 = i' ∧ b.1 .z1 = j' ∧ b.1 .z2 = j' ∧
      b.1 .z3 = j') :
    i - j = i' - j' := by sorry

end RobotMP.W1Hard
