-- Prove2me | Theorems.Thm_SelectedSubset3SUM_Integer_Supplement_theorem_4_8
-- name    : SelectedSubset3SUM.Integer.Supplement.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:52:06.349024+00:00
-- url     : https://prove2.me/theorems/3dba71c9-5cd9-4999-92f7-18349110ded9
-- title:
--   Theorem 4.8 — deterministic reduction of Real APSP to selected-entries matrix multiplication
-- statement:
--   Let $M$ be a cost profile achieved by a deterministic selected-entries multiplication program (for zero–one matrices, input reading included). For every constant $\delta>0$ there are one deterministic program for the comparison–addition RAM and constants $K>0$, $e$ such that for every $n$, every integer $1\le d\le n$ and every directed graph on $n$ vertices with arbitrary real edge weights and no negative cycle, the program, given $n$, $d$ and the graph, halts within
--
--   $$K\,(1+\log(n+1))^e\left(d^\delta\, n\, M\Bigl(n,\bigl\lceil d^{4+2\delta}\bigr\rceil,n\ \Big|\ \Bigl\lceil \frac{n^2}{d^{1+\delta}}\Bigr\rceil\Bigr)+\frac{n^3}{d^\delta}\right)$$
--
--   steps, and outputs, for every ordered pair of vertices, whether the second is reachable from the first and, if so, the exact shortest-path distance.
--
--   That is, Real APSP is solved in $\widetilde O(d^\delta n M_{\text{selected-entries}}(n,d^{4+2\delta},n\mid n^2/d^{1+\delta})+n^3/d^\delta)$ deterministic time, without random sampling. Together with the selected-entries bound of Alman and Vassilevska Williams it gives Corollary 4.9, a deterministic $O(n^{2.9997})$ Real APSP algorithm.
--
--   Differences from the source:
--   - reading: M_selected-entries(n, d^{4+2δ}, n | n²/d^{1+δ}), the time complexity of selected-entries multiplication → any cost profile M achieved by an actual deterministic program on zero–one instances, whose dense input length is within K·M; evaluated at ⌈d^{4+2δ}⌉ and ⌈n²/d^{1+δ}⌉; reason: the reduction only multiplies adjacency matrices (triangle counts, Lemma 4.7); time includes reading the input, as in the mission's other solver premises; this covers the graph construction the proof charges to each call
--   - generalization: selected-entries multiplication of arbitrary matrices → the premise only on zero–one matrices; reason: a solver for general matrices solves the zero–one ones within the same profile, so the theorem specializes
--   - encoding: Real APSP for a free parameter d, Õ(·) deterministic time → one program per δ for all n and all 1 ≤ d ≤ n (d given as input), deterministic run (all-false coin tape) on the comparison–addition RAM with (n+2)^c-bounded words, within K(1+log(n+1))^e times the expression; reason: d ≤ n is the page's range (Problem 4.3); constants precede n, d and the graph
--   - encoding: Real APSP → the published Real APSP semantics: adjacency matrix with absent edges, arbitrary real weights, no negative cycles, a reachability flag and the exact distance for every ordered pair; reason: the standard problem; parallel edges reduce to their minimum
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, STOC 2027 submission #1421 (October 2026), Theorem 4.8, p.17 (proof: Lemmas 4.4, 4.6, 4.7, pp.15–17), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1421.pdf

import Definitions.Def_SelectedSubset3SUM_Integer_Supplement_SelectedProduct

namespace SelectedSubset3SUM.Integer.Supplement

/-- Theorem 4.8, p.17: given a deterministic selected-entries product solver with cost
profile `M`, for every constant `δ > 0` one deterministic comparison--addition program solves
Real APSP (arbitrary real weights, no negative cycles, all `n²` exact distances with
reachability flags) on every `n`-vertex graph, for every block-size parameter `1 ≤ d ≤ n`, in
`Õ(d^δ n M(n, d^{4+2δ}, n | n²/d^{1+δ}) + n³/d^δ)` time. -/
theorem theorem_4_8 (M : ℕ → ℕ → ℕ → ℕ → ℝ) (hM : SelectedEntriesSolver M) :
    ∀ δ : ℝ, 0 < δ → ∃ (P : RealAPSP.Program) (K : ℝ) (e : ℕ), 0 < K ∧
      ∀ (n d : ℕ), 1 ≤ d → d ≤ n → ∀ w : RealAPSP.Mat ℝ n, RealAPSP.NoNegCycle w →
        RealAPSP.Runs P (n + 2) (apspInts d w) (RealAPSP.valueCells w)
          (K * softLog n e * apspCost M δ n d) (RealAPSP.RealAPSPOutput w) := by sorry

end SelectedSubset3SUM.Integer.Supplement
