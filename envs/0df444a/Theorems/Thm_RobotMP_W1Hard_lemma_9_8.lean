-- Prove2me | Theorems.Thm_RobotMP_W1Hard_lemma_9_8
-- name    : RobotMP.W1Hard.lemma_9_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:42:40.177629+00:00
-- url     : https://prove2.me/theorems/33d4a4d9-cfb3-4c46-b02d-7070463aafd9
-- title:
--   Lemma 9.8 — the odometer carries y from (n, n, n) to (0, 0, 0) while x advances by one, z untouched
-- statement:
--   Consider the synchronizer together with the odometer, with parameter $n$. Let $a$ be a configuration with $c = 0$, $(x_1, x_2, x_3) = (i, i, i)$ for some $i \le n - 2$, $(y_1, y_2, y_3) = (n, n, n)$ and $z_1 = z_2 = z_3$. Then there is a configuration $b$ with
--   $$(x_1, x_2, x_3) = (i+1, i+1, i+1), \qquad (y_1, y_2, y_3) = (0, 0, 0)$$
--   reachable from $a$ by moves through configurations in which $c = 0$ and $z_1, z_2, z_3$ keep the values they have in $a$.
--
--   Together with Lemma 9.6 this connects all balanced configurations with $z = n x + y$.
--
--   Differences from the source:
--   - reading: the constraint lists of pp. 47 and 50 → imposed directly in the extended syntax of p. 44; the constants n − 1, n, 0 appear directly instead of three data variables fixed at those values; reason: the paper reasons about the extended constraints themselves.
--   - reading: the printed odometer constraint "{x1 − x3} ∈ {0, 1}" → x1 − x3 ∈ {0, 1}; reason: obvious typo, the surrounding text says (x1, x2, x3) has one of the forms (i,i,i), (i+1,i,i), (i+1,i+1,i).
--   - reading: "where we haven't changed z1, z2 and z3" → z1, z2, z3 equal their initial values at every configuration of the reconfiguration; reason: the stronger of the two readings, and the one the proof establishes.
-- source:
--   Agarwal, Holmgren, Stade, Near-Optimal Makespan and Parameterized Hardness for Multi-Robot Motion Planning, STOC 2027 submission (manuscript sha256 17b4fe59…), p. 50, Lemma 9.8

import Mathlib
import Definitions.Def_RobotMP_W1Hard_Gadgets

set_option autoImplicit false

namespace RobotMP.W1Hard

/-- Lemma 9.8: keeping `c = 0`, from `(x₁, x₂, x₃) = (i, i, i)` with `i ≤ n − 2`,
`(y₁, y₂, y₃) = (n, n, n)` and `z₁ = z₂ = z₃`, the synchronizer–odometer system reaches
`(x₁, x₂, x₃) = (i + 1, i + 1, i + 1)`, `(y₁, y₂, y₃) = (0, 0, 0)` without ever changing
`z₁, z₂, z₃`. -/
theorem lemma_9_8 (n : ℕ) (a : GConfig OdoData OdoCtrl) (i : ℤ)
    (ha : SyncOdoSystem n a) (hc : a.2 .c = false)
    (hx : a.1 .x1 = i ∧ a.1 .x2 = i ∧ a.1 .x3 = i) (hi : i ≤ (n : ℤ) - 2)
    (hy : a.1 .y1 = n ∧ a.1 .y2 = n ∧ a.1 .y3 = n)
    (hz : a.1 .z1 = a.1 .z2 ∧ a.1 .z2 = a.1 .z3) :
    ∃ b : GConfig OdoData OdoCtrl,
      GReach (fun s => SyncOdoSystem n s ∧ s.2 .c = false ∧
        s.1 .z1 = a.1 .z1 ∧ s.1 .z2 = a.1 .z2 ∧ s.1 .z3 = a.1 .z3) a b ∧
      b.1 .x1 = i + 1 ∧ b.1 .x2 = i + 1 ∧ b.1 .x3 = i + 1 ∧
      b.1 .y1 = 0 ∧ b.1 .y2 = 0 ∧ b.1 .y3 = 0 := by sorry

end RobotMP.W1Hard
