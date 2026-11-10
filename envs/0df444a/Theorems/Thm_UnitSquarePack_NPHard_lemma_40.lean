-- Prove2me | Theorems.Thm_UnitSquarePack_NPHard_lemma_40
-- name    : UnitSquarePack.NPHard.lemma_40
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:19:10.435321+00:00
-- url     : https://prove2.me/theorems/8732d652-979b-47b4-925d-921e09db1db6
-- title:
--   Lemma 40 — the tester inequalities (3)–(6) force exactly one true SWITCH per clause
-- statement:
--   Let $n \in \mathbb N$, $t_i = 3(i+1) + \tfrac12 i(i+1)$ and $t_{-1} = 0$. Let $y_p \in \{0, 1\}$ for $0 \le p < 3n$, and let the crossing values $x(r_{i,j}, c_{p,q})$ and $x(\ell_{3i+m}, c_{p,q})$ lie in $\{0, 1, 2\}$ for every clause $i < n$, every tester row $r_{i,j}$ ($j < 1 + 2t_i$) and literal row $\ell_{3i+m}$ ($m < 3$) of clause $i$, and every tester column $c_{p,q}$ with $p \le i$, $q < 3 + p$. Suppose the tester inequalities (3)–(6) of §4.8 hold.
--
--   **Lemma 40.** Then for every clause $0 \le i < n$,
--   $$y_{3i} + y_{3i+1} + y_{3i+2} = 1 .$$
--
--   In the reduction, $y_{3i+m} = 1$ means that the SWITCH gadget of the $m$-th literal of clause $i$ creates a vertical stack; the lemma says that every perfect packing of the clause components selects exactly one literal per clause, which by Lemma 41 forces a true literal in every clause of the 3SAT instance.
--
--   Differences from the source:
--   - reading: Eq. (6) for 0 ≤ p < n and 0 ≤ q < 3 + i (i unbound) → 0 ≤ q < 3 + p; reason: clause p has exactly 3 + p tester columns (p. 44) and every other sum over tester columns runs to 3 + p − 1; obvious index typo (INSIGHTS I1)
--   - encoding: t_{i−1} in (4), (5) for i = 0 → testerCountPrev 0 = 0; reason: the formula t_i = 3(i + 1) + i(i + 1)/2 gives 0 at i = −1
--   - encoding: y_p ∈ {0, 1} and x(a, b) ∈ {0, 1, 2} (pp. 46, 48) → integer-valued functions with these values assumed on the index ranges that (3)–(6) use; values elsewhere are never read; reason: the inequalities involve only these indices
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 50, Lemma 40; Eqs. (3)–(6), pp. 48, 50

import Mathlib
import Definitions.Def_UnitSquarePack_NPHard_TesterSystem

set_option autoImplicit false

namespace UnitSquarePack.NPHard

/-- Lemma 40: for `y_p ∈ {0, 1}` (`p < 3n`) and crossing values `x ∈ {0, 1, 2}`, the
inequalities (3)–(6) imply `y_{3i} + y_{3i+1} + y_{3i+2} = 1` for every clause `i < n`. -/
theorem lemma_40 (n : ℕ) (y : ℕ → ℤ) (xr : ℕ → ℕ → ℕ → ℕ → ℤ) (xl : ℕ → ℕ → ℕ → ℤ)
    (hy : ∀ p < 3 * n, y p = 0 ∨ y p = 1)
    (hxr : ∀ i < n, ∀ j < 1 + 2 * testerCount i, ∀ p ≤ i, ∀ q < 3 + p,
      0 ≤ xr i j p q ∧ xr i j p q ≤ 2)
    (hxl : ∀ i < n, ∀ m < 3, ∀ p ≤ i, ∀ q < 3 + p,
      0 ≤ xl (3 * i + m) p q ∧ xl (3 * i + m) p q ≤ 2)
    (h : TesterInequalities n y xr xl) :
    ∀ i < n, y (3 * i) + y (3 * i + 1) + y (3 * i + 2) = 1 := by sorry

end UnitSquarePack.NPHard
