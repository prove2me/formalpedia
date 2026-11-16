-- Prove2me | Theorems.Thm_PermSymQuery_Quadratic_Supplement_theorem_1_3
-- name    : PermSymQuery.Quadratic.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:43:03.367905+00:00
-- url     : https://prove2.me/theorems/85dc831c-0b01-471b-91bf-2b62cffde457
-- title:
--   Theorem 1.3 — hypergraph separations $R_{1/3}\ge N^{k-o(1)}$, $Q_{1/3}\le N^{1/2+o(1)}$
-- statement:
--   For every integer $k\ge2$ there are an infinite set $\mathcal N$ of vertex counts and, for each $N\in\mathcal N$, a $k$-uniform hypergraph property $F_N$ on $[N]$ whose promise $D_N$ consists of connected, uncolored, simple $k$-uniform hypergraphs, such that
--   $$R_{1/3}(F_N)\ge N^{k-o(1)},\qquad Q_{1/3}(F_N)\le N^{1/2+o(1)}$$
--   along $\mathcal N$: for every $\delta>0$ there is $N_0$ with
--   $$N^{k-\delta}\le R_{1/3}(F_N)\quad\text{and}\quad Q_{1/3}(F_N)\le N^{1/2+\delta}\qquad\text{for all }N\in\mathcal N,\ N\ge N_0.$$
--   Both complexities are worst-case and have error at most $1/3$ on every promised input, in the ordered-tuple quantum oracle model and the hyperedge-membership classical model.
--
--   This shows that the exponent $2k$ in Theorem 1.2 is nearly tight. It is a companion theorem to the mission's goal, Theorem 1.1, and is not used in its proof.
--
--   Differences from the source:
--   - encoding: an explicit family {F_N} → existence of the family; reason: explicitness has no formal counterpart; the family's properties and bounds are stated in full
--   - encoding: an infinite family {F_N} on N vertices → an infinite set Ns of vertex counts with a promise D N and a property F N on Fin N for each N (unused for N ∉ Ns); reason: the paper's family is indexed by the increasing sequence of vertex counts N = 2^b − 1 + b
--   - encoding: N^{k−o(1)} and N^{1/2+o(1)} → for every δ > 0 there is N0 with N^{k−δ} ≤ R and Q ≤ N^{1/2+δ} for all N ∈ Ns with N ≥ N0; reason: this is the meaning of an o(1) exponent along the family
--   - encoding: R_{1/3}, Q_{1/3} compared with real powers of N → the ℕ∞ complexities cast to ℝ≥0∞ and compared with ENNReal.ofReal of the real powers; reason: an infinite complexity satisfies the lower bound and violates the upper bound, as in the source
--   - encoding: a partial k-uniform hypergraph property f : D ⊆ {0,1}^([N] choose k) → {0,1} → a Bool-valued function on all hypergraphs with HypPermInvariant D f, used only on D; reason: the values of f outside D are never read; every source instance, including the empty promise, is represented
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), Theorem 1.3 (stated PDF p. 4, printed p. 2), restated, PDF p. 31 (printed p. 29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Supplement_Hypergraph

open scoped ENNReal

namespace PermSymQuery.Quadratic.Supplement

/-- Theorem 1.3, PDF p.4 (printed p.2), restated PDF p.31 (printed p.29). The family is
indexed by an infinite set of vertex counts; each `F_N` is a k-uniform hypergraph property on
`[N]` whose promise consists of connected hypergraphs. `N^{k−o(1)}` and `N^{1/2+o(1)}` mean:
for every `δ > 0`, eventually along the family. -/
theorem theorem_1_3 : ∀ k : ℕ, 2 ≤ k →
    ∃ (Ns : Set ℕ) (D : (N : ℕ) → Set (Hypergraph (Fin N) k))
      (F : (N : ℕ) → Hypergraph (Fin N) k → Bool),
      Ns.Infinite ∧
      (∀ N ∈ Ns, HypPermInvariant (D N) (F N) ∧ ∀ H ∈ D N, HConnected H) ∧
      ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N ∈ Ns, N0 ≤ N →
        ENNReal.ofReal ((N : ℝ) ^ ((k : ℝ) - δ)) ≤
            ((HReps (D N) (F N) (1 / 3 : ℝ) : ℕ∞) : ℝ≥0∞) ∧
          ((HQeps (D N) (F N) (1 / 3 : ℝ) : ℕ∞) : ℝ≥0∞) ≤
            ENNReal.ofReal ((N : ℝ) ^ ((1 : ℝ) / 2 + δ)) := by sorry

end PermSymQuery.Quadratic.Supplement
