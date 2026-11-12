-- Prove2me | Theorems.Thm_RobotMP_W1Hard_lemma_9_11
-- name    : RobotMP.W1Hard.lemma_9_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:42:26.765727+00:00
-- url     : https://prove2.me/theorems/c5a76d40-548e-4fd8-a106-c37700ef7a9d
-- title:
--   Lemma 9.11 — the constraint gadget locks (x1, y1) while c = 1 and its reachable locked states are exactly S
-- statement:
--   Let $n \ge 1$ and $S \subseteq \{0, \dots, n-1\}^2$. The constraint gadget for $S$ (synchronizer, odometer and the tester for $\{ni + j : (i,j) \in S\}$) has the data variables $x_1, y_1$ and $8$ internal data variables, the control variable $c$ and $6$ internal control variables, and there is an allowed initial configuration $\iota$ such that
--   - while $c = 1$, $x_1$ and $y_1$ cannot change: every move from an allowed configuration with $c = 1$ keeps $x_1$ and $y_1$;
--   - every configuration with $c = 1$ reachable from $\iota$ has $(x_1, y_1) \in S$;
--   - for each $(i, j) \in S$ some configuration with $c = 1$, $x_1 = i$, $y_1 = j$ is reachable from $\iota$.
--
--   The gadget enforces an arbitrary binary relation on two data variables using only monotone constraints; it is the core of the W[1]-hardness of CMR.
--
--   Differences from the source:
--   - reading: "there is a constraint gadget" → the concrete gadget of pp. 47–52 with an initial configuration chosen existentially, "reachable" meaning reachable from it; reason: the gadget the proof constructs, and the brief requires the concrete system.
--   - reading: "8 internal data variables and 6 internal control variables" → the gadget's variable types have 2 + 8 and 1 + 6 elements, counted under the extended syntax of p. 44 (auxiliary and constant-valued variables not counted); reason: the count matches x2, x3, y2, y3, z1, z2, z3, w1 and q, r1, r2, r3, p1, p2 of Figure 11.
--   - reading: "while c = 1, x1 and y1 cannot change" → for every move from any allowed configuration with c = 1, not only reachable ones; reason: the stronger reading, true by the locking constraints.
--   - encoding: no hypothesis on n → 0 < n; reason: x1 ranges over {0, …, n − 1}, so for n = 0 the gadget has no configuration at all (an undefined case).
-- source:
--   Agarwal, Holmgren, Stade, Near-Optimal Makespan and Parameterized Hardness for Multi-Robot Motion Planning, STOC 2027 submission (manuscript sha256 17b4fe59…), p. 52, Lemma 9.11

import Mathlib
import Definitions.Def_RobotMP_W1Hard_Gadgets

set_option autoImplicit false

namespace RobotMP.W1Hard

open Set

/-- Lemma 9.11: for `S ⊆ {0, …, n − 1}²`, the constraint gadget (synchronizer, odometer and
tester; exposed data variables `x₁, y₁`, exposed control `c`, eight internal data variables and
six internal control variables) has an initial configuration such that: while `c = 1`, no move
changes `x₁` or `y₁`; every configuration with `c = 1` reachable from it has `(x₁, y₁) ∈ S`; and
for each `(i, j) ∈ S` some configuration with `c = 1`, `x₁ = i`, `y₁ = j` is reachable. -/
theorem lemma_9_11 (n : ℕ) (hn : 0 < n) (S : Set (ℤ × ℤ))
    (hS : S ⊆ Icc 0 ((n : ℤ) - 1) ×ˢ Icc 0 ((n : ℤ) - 1)) :
    Nat.card GadgetData = 2 + 8 ∧ Nat.card GadgetCtrl = 1 + 6 ∧
    ∃ init : GConfig GadgetData GadgetCtrl, ConstraintGadget n S init ∧
      (∀ a b : GConfig GadgetData GadgetCtrl, GStep (ConstraintGadget n S) a b →
        a.2 .c = true → b.1 .x1 = a.1 .x1 ∧ b.1 .y1 = a.1 .y1) ∧
      (∀ b : GConfig GadgetData GadgetCtrl, GReach (ConstraintGadget n S) init b →
        b.2 .c = true → (b.1 .x1, b.1 .y1) ∈ S) ∧
      (∀ p ∈ S, ∃ b : GConfig GadgetData GadgetCtrl, GReach (ConstraintGadget n S) init b ∧
        b.2 .c = true ∧ b.1 .x1 = p.1 ∧ b.1 .y1 = p.2) := by sorry

end RobotMP.W1Hard
