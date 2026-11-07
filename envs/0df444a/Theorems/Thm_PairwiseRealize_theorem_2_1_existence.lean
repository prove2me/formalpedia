-- Prove2me | Theorems.Thm_PairwiseRealize_theorem_2_1_existence
-- name    : PairwiseRealize.theorem_2_1_existence
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:47.886125+00:00
-- url     : https://prove2.me/theorems/f232d832-5d4d-4dee-814e-19be0c4347dc
-- title:
--   Theorem 2.1, first sentence, p.4 (existence clause; the whole theorem is the goal `PairwiseRealize.theorem_2_1`)
-- statement:
--   There are an absolute constant $C$ and $n_0$ such that for every $n\ge n_0$, every forbidden set $D\subseteq V$ with $|D|\le N/4096$, with $U=V\setminus D$, and every integer target $b\in\mathbb Z^m$ with $y_U\in P_U$ and $\operatorname{depth}_U(y_U)\ge Cn^2\log(n+1)$, there is a set $S\subseteq U$ of distinct rows with
--
--   $$\sum_{x\in S}w_x=b.$$
--
--   This is the first of the two sentences of Theorem 2.1. The goal states both.
--
--   Differences from the source:
--   - encoding: the whole of Theorem 2.1 (two sentences) → the first sentence; the second is stated in the goal `PairwiseRealize.theorem_2_1`; reason: a named intermediate target of the goal; the mission states the full theorem as its goal
--   - encoding: log(n + 1), base unspecified → the natural logarithm; reason: another base changes only C
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), Theorem 2.1, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_PairwiseRealize_Model

namespace PairwiseRealize

/-- **Theorem 2.1, first sentence (existence clause), p.4 (PDF p.5).** K. Shi, H. Sun, *Robust Exact
Realization of Pairwise Boolean Statistics*, STOC 2027 submission (manuscript sha256 62090516…):
"There is an absolute constant C such that, for all sufficiently large n, the following holds. Let
D ⊆ V be any forbidden set with |D| ≤ εN, where ε = 1/4096, and let U = V ∖ D. Every integer target
b ∈ ℤ^m whose centered vector y_U from (2.3) lies in P_U and satisfies depth_U(y_U) ≥ Cn² log(n + 1)
has an exact realization by distinct rows from U."

This is the first of the two sentences of Theorem 2.1; the goal `theorem_2_1` states both (with the
Las Vegas algorithm). -/
theorem theorem_2_1_existence :
    ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ D : Finset (Row n), 4096 * D.card ≤ 2 ^ n →
      ∀ b : Feat n → ℤ,
        centered n (Finset.univ \ D) b ∈ zonotope n (Finset.univ \ D) →
        C * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1) ≤
          depth n (Finset.univ \ D) (centered n (Finset.univ \ D) b) →
        ∃ S, IsRealization n (Finset.univ \ D) b S := by sorry

end PairwiseRealize
