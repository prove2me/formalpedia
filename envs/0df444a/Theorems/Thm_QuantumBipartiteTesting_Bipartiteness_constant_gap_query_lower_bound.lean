-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_constant_gap_query_lower_bound
-- name    : QuantumBipartiteTesting.Bipartiteness.constant_gap_query_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:07:56.727132+00:00
-- url     : https://prove2.me/theorems/5003deee-aa90-4869-a81a-945bf1c87095
-- title:
--   A constant feasible signing gap forces the near-optimal quantum query bound
-- statement:
--   There are absolute constants $c>0$ and $N_0\ge2$ such that the following holds for every $N\ge N_0$. Fix an encoding, an actual finite quantum circuit with $q$ queries to the three-color signed adjacency oracle, and a computational-basis output event. If its feasible YES-minus-NO acceptance gap at the center distribution satisfies
--
--   $$
--   \Delta_{\mathrm{feas}}(M_0,1)\ge\frac14,
--   $$
--
--   then
--
--   $$
--   q\ge c\frac{N^{1/3}}{\log N}.
--   $$
--
--   The constants precede all input sizes and circuit data. This is the analytic lower-bound step: it converts a constant distinguishing gap on the concrete hidden-block distributions into an operational quantum query lower bound, with arbitrary finite workspace and both signing laws retained.
-- source:
--   Kayal–Sen–Szabó, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, §3.5 proof of Theorem 3.2, equations (22)–(28), printed pp.19–20, using Proposition 3.13 and Lemma 3.15. This variant retains the polynomial factor of l and uses the zero-anchored grid estimate, so a center gap of 1/4 suffices without error amplification.

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
open QuantumBipartiteTesting.Bipartiteness
open scoped BigOperators Classical

theorem QuantumBipartiteTesting.Bipartiteness.constant_gap_query_lower_bound : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ k w q : ℕ,
    ∀ E : Encoding (Fin N × Bool) k, ∀ A : Algorithm (Address N 3) k w q,
    ∀ out : (Address N 3 × Bits k) × Fin w → Bool,
      (1/4:ℝ) ≤ FeasibleGap E A out (Center N) 1 → c*LowerBoundScale N ≤ (q:ℝ) := by sorry
