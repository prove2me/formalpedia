-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_Supplement_lemma_6
-- name    : TwoOptAllExp.TSP.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:44:57.394632+00:00
-- url     : https://prove2.me/theorems/4f04946f-14b5-48db-b634-807c72e4496c
-- title:
--   Lemma 6 — from zero, $S_n$ is the unique maximal improving flip sequence of $I_n$; unit gains; $8\cdot2^n-6$ flips
-- statement:
--   Let $I_n$ ($n\ge0$) be the $(3,2,2)$-MCA instance of Section 3 and $\sigma_0$ the all-zero assignment. Let $S_0=(v_{0,1},v_{0,6})$ and $S_i=(v_{i,1},S_{i-1},v_{i,2},v_{i,3},S_{i-1},v_{i,4},v_{i,5},v_{i,6})$ for $i\ge1$. Then:
--
--   1. a flip sequence $Y$ is a maximal improving flip sequence from $\sigma_0$ if and only if $Y=S_n$;
--   2. every flip of $S_n$ increases the objective value by exactly $1$;
--   3. $$|S_n|=8\cdot2^n-6.$$
--
--   This is the exponential lower bound behind Theorem 2: every pivot rule performs exactly these flips.
--
--   Differences from the source:
--   - encoding: the unique maximal improving flip sequence is S_n → ∀ ys, IsMaximalFlipSeq Φ σ₀ ys ↔ ys = S n n; reason: existence and uniqueness together
--   - encoding: every flip increases the objective by exactly 1 → Φ after the first k+1 flips of S_n equals Φ after the first k flips plus 1, for every k < |S_n|; reason: the same statement flip by flip
--   - encoding: number of flips 8·2^n − 6 → length of S_n cast to ℤ equals 8·2^n − 6; reason: integer arithmetic, no truncated subtraction
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Lemma 6, p. 9 (proof pp. 10–12)

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA322

namespace TwoOptAllExp.TSP.Supplement

open MCA322

/-- **Lemma 6** (p. 9). Starting from the all-zero assignment, the unique maximal improving flip
sequence of the (3,2,2)-MCA instance `I_n` of Section 3 is `S_n`, given recursively by
`S_0 = (v_{0,1}, v_{0,6})` and `S_i = (v_{i,1}, S_{i-1}, v_{i,2}, v_{i,3}, S_{i-1}, v_{i,4}, v_{i,5}, v_{i,6})`.
Every flip in this sequence increases the objective value by exactly `1`, and the number of flips
is `8 · 2^n - 6`. -/
theorem lemma_6 (n : ℕ) :
    (∀ ys : List (Fin (6 * n + 2)),
      IsMaximalFlipSeq (inst n).Φ (σ₀ n) ys ↔ ys = S n n) ∧
    (∀ k < (S n n).length,
      (inst n).Φ (applyFlips (σ₀ n) ((S n n).take (k + 1))) =
        (inst n).Φ (applyFlips (σ₀ n) ((S n n).take k)) + 1) ∧
    ((S n n).length : ℤ) = 8 * 2 ^ n - 6 := by sorry

end TwoOptAllExp.TSP.Supplement
