-- Prove2me | Theorems.Thm_Problem97_counting_arithmetic
-- name    : Problem97.counting_arithmetic
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:57:09.002706+00:00
-- url     : https://prove2.me/theorems/c7a2209d-02e3-428d-ac6a-3b642f4a8841
-- title:
--   The isosceles-count inequality forces the nine-vertex threshold
-- statement:
--   Let $n$ be a natural number with $n\ge 3$. If the lower and upper isosceles-count estimates give $$6n\le \frac{11n^2-18n}{12},$$ then $n\ge 9$. This isolates the arithmetic finalization of the counting obstruction from its geometric input.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_counting_arithmetic.lean#L1-L32

/- Generated theorem stub from Erdos9796Proof.P97.CountingArithmetic by Stage 2 proof cut; source SHA-256 fbcea1f88d69889eb703a9666ba5be87cc47b69941cbca63e4dba5d53dd10763 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
open Problem97



/-!
# Counting-obstruction arithmetic core (Milestone 3 sub-step)

The arithmetic half of Dumitrescu's `n ≥ 9` bound: given the isosceles
inequality

`6 * n  ≤  (11 * n^2 − 18 * n) / 12`

on natural `n ≥ 3`, conclude `9 ≤ n`.  The geometric half — establishing
the inequality from `HasNEquidistantProperty 4` on a convex point set
— is `p97-dumitrescu-inequality` (still open).

-/

theorem Problem97.counting_arithmetic {n : ℕ} (hn : 3 ≤ n)
    (h : (6 : ℝ) * n ≤ ((11 : ℝ) * n ^ 2 - 18 * n) / 12) :
    9 ≤ n := by sorry
