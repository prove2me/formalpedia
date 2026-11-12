-- Prove2me | Theorems.Thm_RobotMP_W1Hard_lemma_9_6
-- name    : RobotMP.W1Hard.lemma_9_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:42:30.289572+00:00
-- url     : https://prove2.me/theorems/358025bb-a72b-4741-97fd-f61318d40a07
-- title:
--   Lemma 9.6 — the synchronizer moves the y- and z-blocks together when q = 0 and the y-block alone when q = 1
-- statement:
--   Consider the synchronizer constraint system with parameter $n$ (data variables $y_1, y_2, y_3 \in \{0, \dots, n\}$, $z_1, z_2, z_3 \in \{0, \dots, n^2 - 1\}$, controls $c, q, r_1, r_2, r_3$).
--   1. Let $a$ and $b$ be configurations with $c = q = 0$, $a$ having $(y_1, y_2, y_3) = (i, i, i)$ and $(z_1, z_2, z_3) = (j, j, j)$, $b$ having $(y_1, y_2, y_3) = (i', i', i')$ and $(z_1, z_2, z_3) = (j', j', j')$, where $j' - i' = j - i$. Then $b$ is reachable from $a$ by moves through configurations with $c = q = 0$.
--   2. Let $a$ and $b$ be configurations with $c = 0$, $q = 1$, $a$ having $y = (i,i,i)$, $z = (j,j,j)$ and $b$ having $y = (i', i', i')$, $z = (j, j, j)$. Then $b$ is reachable from $a$ by moves through configurations with $c = 0$, $q = 1$.
--
--   The synchronizer keeps $z_1 - y_1$ fixed while $q = 0$, which lets the constraint gadget track $n x_1 + y_1$ in $z_1$.
--
--   Differences from the source:
--   - reading: the synchronizer's constraint list of p. 47 → imposed directly in the extended syntax of p. 44, without the auxiliary variables that simulate it; reason: the paper reasons about the extended constraints themselves.
--   - reading: "configuration" and "keeping c = 0 and q = 0" → configurations satisfying every synchronizer constraint, with c = q = 0 at every configuration of the reconfiguration; reason: the paper's meaning of keeping a variable fixed.
-- source:
--   Agarwal, Holmgren, Stade, Near-Optimal Makespan and Parameterized Hardness for Multi-Robot Motion Planning, STOC 2027 submission (manuscript sha256 17b4fe59…), p. 48, Lemma 9.6

import Mathlib
import Definitions.Def_RobotMP_W1Hard_Gadgets

set_option autoImplicit false

namespace RobotMP.W1Hard

/-- Lemma 9.6: with `c = 0` and `q = 0` held, the synchronizer moves the `y`-block and the
`z`-block together (any balanced configuration with the same `j − i` is reachable); with `c = 0`
and `q = 1` held, the `y`-block moves alone while the `z`-block keeps its value. -/
theorem lemma_9_6 (n : ℕ) :
    (∀ (a b : GConfig SyncData SyncCtrl) (i j i' j' : ℤ),
      SyncSystem n a → a.2 .c = false → a.2 .q = false →
      a.1 .y1 = i → a.1 .y2 = i → a.1 .y3 = i → a.1 .z1 = j → a.1 .z2 = j → a.1 .z3 = j →
      SyncSystem n b → b.2 .c = false → b.2 .q = false →
      b.1 .y1 = i' → b.1 .y2 = i' → b.1 .y3 = i' → b.1 .z1 = j' → b.1 .z2 = j' →
      b.1 .z3 = j' → j' - i' = j - i →
      GReach (fun s => SyncSystem n s ∧ s.2 .c = false ∧ s.2 .q = false) a b) ∧
    (∀ (a b : GConfig SyncData SyncCtrl) (i j i' : ℤ),
      SyncSystem n a → a.2 .c = false → a.2 .q = true →
      a.1 .y1 = i → a.1 .y2 = i → a.1 .y3 = i → a.1 .z1 = j → a.1 .z2 = j → a.1 .z3 = j →
      SyncSystem n b → b.2 .c = false → b.2 .q = true →
      b.1 .y1 = i' → b.1 .y2 = i' → b.1 .y3 = i' → b.1 .z1 = j → b.1 .z2 = j →
      b.1 .z3 = j →
      GReach (fun s => SyncSystem n s ∧ s.2 .c = false ∧ s.2 .q = true) a b) := by sorry

end RobotMP.W1Hard
