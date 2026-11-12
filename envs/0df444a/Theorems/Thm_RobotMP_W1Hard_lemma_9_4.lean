-- Prove2me | Theorems.Thm_RobotMP_W1Hard_lemma_9_4
-- name    : RobotMP.W1Hard.lemma_9_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:42:38.458968+00:00
-- url     : https://prove2.me/theorems/3c3c7209-a8ab-4401-91ca-350b72f05a96
-- title:
--   Lemma 9.4 — a connected set is bimonotone iff all its row and column sections are connected
-- statement:
--   Let $I_1 = \{a_1, \dots, b_1\}$ and $I_2 = \{a_2, \dots, b_2\}$ be discrete intervals and let $S \subseteq I_1 \times I_2$ be connected (by unit steps inside $S$). Then
--   $$S \text{ is bimonotone} \iff \text{for all } x \in I_1,\ y \in I_2:\ (\{x\} \times I_2) \cap S \text{ and } (I_1 \times \{y\}) \cap S \text{ are connected.}$$
--
--   The lemma is the practical test for bimonotonicity used to admit the gadget constraints (e.g. $u - v \in \{0,1\}$ and the tester set) as CMS constraints.
--
--   Differences from the source:
--   - encoding: discrete intervals I1, I2 → integer intervals Icc a b in ℤ, and empty sections count as connected; reason: Lean convention; the paper's definition of connected is vacuous on the empty set.
-- source:
--   Agarwal, Holmgren, Stade, Near-Optimal Makespan and Parameterized Hardness for Multi-Robot Motion Planning, STOC 2027 submission (manuscript sha256 17b4fe59…), p. 42, Lemma 9.4

import Mathlib
import Definitions.Def_RobotMP_W1Hard_Bimonotone

set_option autoImplicit false

namespace RobotMP.W1Hard

open Set

/-- Lemma 9.4: a connected `S ⊆ I₁ × I₂` is bimonotone iff all its row and column sections are
connected. -/
theorem lemma_9_4 (a₁ b₁ a₂ b₂ : ℤ) (S : Set (ℤ × ℤ)) (hS : S ⊆ Icc a₁ b₁ ×ˢ Icc a₂ b₂)
    (hconn : IsGridConnected S) :
    IsBimonotone (Icc a₁ b₁) (Icc a₂ b₂) S ↔
      ∀ x ∈ Icc a₁ b₁, ∀ y ∈ Icc a₂ b₂,
        IsGridConnected (({x} ×ˢ Icc a₂ b₂) ∩ S) ∧ IsGridConnected ((Icc a₁ b₁ ×ˢ {y}) ∩ S) := by sorry

end RobotMP.W1Hard
