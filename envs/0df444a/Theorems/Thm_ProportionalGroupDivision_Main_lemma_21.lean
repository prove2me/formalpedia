-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_lemma_21
-- name    : ProportionalGroupDivision.Main.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:10.979427+00:00
-- url     : https://prove2.me/theorems/0bf406c0-2041-4d34-8dca-9c690f5310cf
-- title:
--   Lemma 21 (Beck–Fiala) — exact linear rounding to at most $n$ fractional coordinates
-- statement:
--   Let $m>n>0$ be integers, $A\in[0,1]^{n\times m}$ and $x\in[0,1]^m$. Then there is $x'\in[0,1]^m$ with
--
--   $$Ax=Ax'$$
--
--   such that all but $n$ coordinates of $x'$ are rounded, i.e. at most $n$ coordinates of $x'$ lie outside $\{0,1\}$.
--
--   Every row value is preserved exactly; the lemma reduces the rounding in Theorem 6 to the case $m\le n$.
--
--   Differences from the source:
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Lemma 21, PDF p. 20 = printed p. 20

import Mathlib

open scoped BigOperators

namespace ProportionalGroupDivision.Main

/-- Lemma 21 (Beck–Fiala, PDF p. 20): for integers `m > N > 0`, a matrix `A ∈ [0,1]^{N×m}` and a
point `x ∈ [0,1]^m` there is `x′ ∈ [0,1]^m` with `A x = A x′` such that all but `N` coordinates of
`x′` are rounded (equal to `0` or `1`). -/
theorem lemma_21 (N m : ℕ) (hN : 0 < N) (hNm : N < m) (A : Matrix (Fin N) (Fin m) ℝ)
    (hA : ∀ i g, A i g ∈ Set.Icc (0 : ℝ) 1) (x : Fin m → ℝ) (hx : ∀ g, x g ∈ Set.Icc (0 : ℝ) 1) :
    ∃ x' : Fin m → ℝ, (∀ g, x' g ∈ Set.Icc (0 : ℝ) 1) ∧ A.mulVec x = A.mulVec x' ∧
      (Finset.univ.filter (fun g => x' g ≠ 0 ∧ x' g ≠ 1)).card ≤ N := by sorry

end ProportionalGroupDivision.Main
