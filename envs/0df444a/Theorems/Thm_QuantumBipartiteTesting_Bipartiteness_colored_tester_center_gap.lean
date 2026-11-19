-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_colored_tester_center_gap
-- name    : QuantumBipartiteTesting.Bipartiteness.colored_tester_center_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:13:07.455206+00:00
-- url     : https://prove2.me/theorems/ba6b293e-6b75-4c80-a87e-a4f25e8cdc72
-- title:
--   Balancedness testing promises force a constant feasible center gap
-- statement:
--   There is an absolute $N_0\ge120$ with the following property. Let $N\ge N_0$ and $0<\varepsilon\le1/300$. Suppose an actual quantum circuit on the three-color signed adjacency oracle accepts every balanced consistent colored graph with probability at least $2/3$, and accepts every consistent graph with frustration at least $3\varepsilon N$ with probability at most $1/3$. Then its feasible distributional signing gap satisfies
--
--   $$
--   \Delta_{\mathrm{feas}}(M_0,1)\ge\frac14.
--   $$
--
--   All encodings, finite workspaces, query counts and computational-basis output events are allowed. The threshold is chosen before all circuit data. This is the concrete testing-promise interface for the analytic query lower bound.
-- source:
--   Kayal–Sen–Szabó, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, §3.1 center hard distribution and deterministic edge count (also described in the introduction), Lemma 3.3 and Remark 3.4, printed pp.12–14; used in §3.5 Theorem 3.2. Explicit epsilon<=1/300 and gap1/4 retain the given two-sided error without amplification.

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
open QuantumBipartiteTesting.Bipartiteness
open scoped BigOperators Classical

theorem QuantumBipartiteTesting.Bipartiteness.colored_tester_center_gap : ∃ N₀ : ℕ, 120 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ ε : ℝ, 0 < ε → ε ≤ 1/300 →
    ∀ k w q : ℕ, ∀ E : Encoding (Fin N × Bool) k, ∀ A : Algorithm (Address N 3) k w q,
    ∀ out : (Address N 3 × Bits k) × Fin w → Bool,
      (∀ F : Finset (ColoredEdge N), Consistent F → ∀ b : ColoredEdge N → Bool,
        (Balanced F b → 2/3 ≤ Accept E A out (LiftOracle (SignedResponse F b))) ∧
        (ε*N*3 ≤ (Frustration F b:ℝ) → Accept E A out (LiftOracle (SignedResponse F b)) ≤ 1/3)) →
      (1/4:ℝ) ≤ FeasibleGap E A out (Center N) 1 := by sorry
