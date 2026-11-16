-- Prove2me | Theorems.Thm_SelectedSubset3SUM_Integer_Supplement_theorem_5_9
-- name    : SelectedSubset3SUM.Integer.Supplement.theorem_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:52:41.455228+00:00
-- url     : https://prove2.me/theorems/f13d917c-5a20-4a49-9cb7-45d4dce1f068
-- title:
--   Theorem 5.9 — deterministic reduction of Real 3SUM to selected-entries matrix multiplication
-- statement:
--   Let $M$ be a cost profile achieved by a deterministic selected-entries multiplication program (for zero–one matrices, input reading included). For every constant $\delta>0$ there are one deterministic program for the comparison–addition RAM and constants $K>0$, $e$ such that for every $n$, every integer $1\le d\le n$ and all lists $A,B,C$ of at most $n$ real numbers each, the program, given $n$, $d$, the lengths and the numbers, halts within
--
--   $$K\,(1+\log(n+1))^e\left(d^\delta\, M\Bigl(n,\bigl\lceil d^{12+2\delta}\bigr\rceil,n\ \Big|\ \Bigl\lceil \frac{n^2}{d^{1+\delta}}\Bigr\rceil\Bigr)+\frac{n^2}{d^\delta}\right)$$
--
--   steps and correctly reports whether $a+b=c$ for some $a\in A$, $b\in B$, $c\in C$. Equal sums and repeated values are allowed.
--
--   That is, Real 3SUM is solved in $\widetilde O(d^\delta M_{\text{selected-entries}}(n,d^{12+2\delta},n\mid n^2/d^{1+\delta})+n^2/d^\delta)$ deterministic time. Together with the selected-entries bound of Alman and Vassilevska Williams it gives Corollary 5.10, a deterministic $O(n^{1.9998})$ Real 3SUM algorithm.
--
--   Differences from the source:
--   - reading: M_selected-entries(n, d^{12+2δ}, n | n²/d^{1+δ}) → any cost profile M achieved by an actual deterministic program on zero–one instances, whose dense input length is within K·M; evaluated at ⌈d^{12+2δ}⌉ and ⌈n²/d^{1+δ}⌉; reason: the reduction only counts triangles (Lemma 5.8); time includes reading the input, as in the mission's other solver premises
--   - generalization: selected-entries multiplication of arbitrary matrices → the premise only on zero–one matrices; reason: a solver for general matrices solves the zero–one ones within the same profile, so the theorem specializes
--   - generalization: sets A, B, C of O(n) real numbers → arbitrary real lists of length at most n each, repetitions allowed; reason: every set of size at most n is such a list; a set of size cn splits into constantly many instances of size n
--   - encoding: Real 3SUM for a parameter d, Õ(·) deterministic time → one program per δ for all n and all 1 ≤ d ≤ n (d given as input), deterministic run on the comparison–addition RAM with (n+2)^c-bounded words, within K(1+log(n+1))^e times the expression, answer in output cell 0; reason: d ≤ n is the page's range (§5, p.18); constants precede n, d and the input
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, STOC 2027 submission #1421 (October 2026), Theorem 5.9, p.21 (proof: Problem 5.1 reduction p.18, Lemmas 5.3, 5.5, 5.7, 5.8, pp.18–21; the wanted-entry count n²/d^(1+δ) as in the proof of Lemma 5.8, p.21), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1421.pdf

import Definitions.Def_SelectedSubset3SUM_Integer_Supplement_SelectedProduct

namespace SelectedSubset3SUM.Integer.Supplement

/-- Theorem 5.9, p.21: given a deterministic selected-entries product solver with cost
profile `M`, for every constant `δ > 0` one deterministic comparison--addition program decides
Real 3SUM for arbitrary real lists `A, B, C` of length at most `n` (ties and repetitions
allowed), for every block-size parameter `1 ≤ d ≤ n`, in
`Õ(d^δ M(n, d^{12+2δ}, n | n²/d^{1+δ}) + n²/d^δ)` time. -/
theorem theorem_5_9 (M : ℕ → ℕ → ℕ → ℕ → ℝ) (hM : SelectedEntriesSolver M) :
    ∀ δ : ℝ, 0 < δ → ∃ (P : RealAPSP.Program) (K : ℝ) (e : ℕ), 0 < K ∧
      ∀ (n d : ℕ), 1 ≤ d → d ≤ n → ∀ A B C : List ℝ,
        A.length ≤ n → B.length ≤ n → C.length ≤ n →
        RealAPSP.Runs P (n + 2) (threeSumInts n d A B C) (threeSumReals A B C)
          (K * softLog n e * threeSumCost M δ n d) (ThreeSumOutput A B C) := by sorry

end SelectedSubset3SUM.Integer.Supplement
