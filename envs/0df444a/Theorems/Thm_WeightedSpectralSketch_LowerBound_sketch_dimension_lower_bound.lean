-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_sketch_dimension_lower_bound
-- name    : WeightedSpectralSketch.LowerBound.sketch_dimension_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:01:14.190997+00:00
-- url     : https://prove2.me/theorems/c22987ce-7c5f-4005-acf5-dbe6bcd82ee8
-- title:
--   Theorem 1.1 — weighted spectral sparsification by linear sketches needs dimension $\Omega(n^{6/5})$
-- statement:
--   There are absolute constants $c>0$ and $n_0$ such that the following holds for every $n\ge n_0$. Let a randomized linear sketch of dimension $N$ draw a real matrix $A\in\mathbb R^{N\times\binom n2}$ from an arbitrary distribution independent of the input, observe $Aw$, and output a symmetric matrix $\widehat L$ computed from $A$, $Aw$ and internal randomness. Suppose that for **every** $n$-vertex real weighted graph $w\in\mathbb R_{\ge0}^{\binom{[n]}2}$ with positive-weight ratio $w_{\max}/w_{\min}\le4n^5$,
--
--   $$
--   \Pr\Big[(1-0.01)\,x^\top L_wx\le x^\top\widehat Lx\le(1+0.01)\,x^\top L_wx\ \text{ for all }x\in\mathbb R^n\Big]\ge0.99 .
--   $$
--
--   Then
--
--   $$
--   N\ge c\,n^{6/5}.
--   $$
--
--   The constants come before the sketch, the recovery and the input. The output may be any symmetric matrix: it need not be sparse, a Laplacian, or supported on the input edges. The weights are arbitrary nonnegative reals within the ratio bound, the graphs need not be connected, and recovery need not be linear or continuous.
--
--   The bound matches the $\widetilde O(n^{6/5})$ upper bound of Chen, Khanna and Li (FOCS 2022) up to polylogarithmic factors. It removes their restriction to incidence sketches, and together with their $\widetilde O(n)$ bound for cut sparsification it separates cut from spectral sparsification in the linear sketching model.
--
--   **Formalization Note.** The source's $w_{\max}/w_{\min}=O(n^5)$ is instantiated by the explicit envelope $4n^5$ satisfied by the hard instances (p. 22). Admissibility is stated as: some $a>0$ has every coordinate in $\{0\}\cup[a,4n^5a]$, so the empty graph is allowed. The success event is one event for all real $x$. $\Omega(n^{6/5})$ is stated with constants uniform in the sketch; the source's proof (pp. 26–27, including padding by isolated vertices) gives, for example, $n_0=2\cdot10^7(10^8+2)^5$ and $c=10^{-12}/\big((10^8+2)(2\cdot10^7)^{1/5}32^{6/5}\big)$.
--
--   Differences from the source:
--
--   - reading: w_max/w_min = O(n^5) → positive-weight ratio at most 4n^5 (some a > 0 with every coordinate in {0} ∪ [a, 4n^5 a]); reason: 4n^5 is the explicit envelope the source proves for its hard instances (p. 22), and the theorem only needs success on that envelope; this is the strongest form of the O(n^5) hypothesis the source establishes
--   - encoding: N = Ω(n^{6/5}) → ∃ c > 0, ∃ n_0, ∀ n ≥ n_0 and every sketch: c n^{6/5} ≤ N; reason: the definition of Ω with constants uniform in the sketch, recovery and input; the source's padding step covers every large n
--   - encoding: a random sketch matrix independent of the input, and a recovery algorithm using A, Aw and internal randomness → one seed ω of an arbitrary probability space determines a measurable A(ω) and a jointly measurable recovery D(ω, ·); reason: the standing measurability convention of a probability experiment; independent recovery randomness is the special case of a product seed
--   - encoding: edge-weight vector in ℝ^{binom(n,2)} → a function on the off-diagonal Sym2 elements of Fin n; reason: same coordinates
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 3, Theorem 1.1 (proof pp. 26–27; ratio bound p. 22), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph

open MeasureTheory Matrix
open scoped ENNReal

universe u

namespace WeightedSpectralSketch.LowerBound

/-- Theorem 1.1, p. 3: there are absolute constants `c > 0` and `n₀` such that for every `n ≥ n₀`,
every randomized linear sketch of dimension `N` (an arbitrary sampled real matrix and an arbitrary
measurable recovery) that computes a `(1 ± 0.01)`-spectral sparsifier with probability at least
`0.99` on every `n`-vertex real weighted graph with positive-weight ratio at most `4 n⁵` satisfies
`N ≥ c n^{6/5}`. -/
theorem sketch_dimension_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (N : ℕ) (Ω : Type u) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (S : LinearSketch (Fin n) N Ω),
      (∀ w : EdgeSlot (Fin n) → ℝ, RatioAdmissible (4 * (n : ℝ) ^ 5) w →
        (99 / 100 : ℝ≥0∞) ≤ successProb P S (1 / 100) w) →
      c * (n : ℝ) ^ ((6 : ℝ) / 5) ≤ N := by sorry

end WeightedSpectralSketch.LowerBound
