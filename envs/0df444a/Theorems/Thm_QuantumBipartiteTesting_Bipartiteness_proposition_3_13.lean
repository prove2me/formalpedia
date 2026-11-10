-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_proposition_3_13
-- name    : QuantumBipartiteTesting.Bipartiteness.proposition_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:13:03.173501+00:00
-- url     : https://prove2.me/theorems/51528e18-e60a-44ad-bcf5-2e92dcc4836c
-- title:
--   Proposition 3.13 — feasible rational acceptance gap
-- statement:
--   There are positive absolute constants controlling the degree and the sufficiently small query range. For every actual circuit and every query count, there is a polynomial $H$ with degree $O(q\log q)$ such that, at every grid pair away from denominator poles,
--   $$\Delta(M,\ell)=\frac{\ell H(M,\ell)}{D_q(M,\ell)}+\eta(M,\ell).$$
--   The error is the actual difference of feasible and formal gaps and tends uniformly to zero for $q\le c_0N^{1/3}/\log N$. In that sufficiently small query range, $D_q$ is nonzero everywhere on the grid for all sufficiently large input sizes. The polynomial depends on the circuit, not on the grid point. This is the rational approximation to actual acceptance used in the outer lower-bound argument.
--
--   Differences from the source:
--   - encoding: finite quantum query circuits with binary encoded outcomes and arbitrary workspace → published QueryAlg, arbitrary finite complex registers, injective null-zero bit encoding, unitary XOR oracle, input-independent output event; reason: every finite workspace is represented up to a basis bijection; unused answer bit strings and dummy vertex queries are retained
--   - encoding: degree O(q log q) → a positive universal multiple of 1 + q log(q+2); reason: the two rates agree as q tends to infinity; the globally defined expression also retains q=0 and q=1 without artificial hypotheses
--   - reading: formal expectation described both by (A.2)–(A.4) and by arbitrary output on overflow → the algebraic partition functional (A.2)–(A.4), followed by signing probabilities and linear extension; reason: these descriptions disagree at N=M=4,l=2: a one-edge moment is 1/2 algebraically versus 1/8 with empty output on overflow; the feasible law stays conditional and its comparison remains a theorem
--   - reading: Definition 3.6 gives structural matching/response consistency and calls it equivalent to positive sampling probability → consistency is the structural condition, without a parameter-dependent positivity certificate; reason: a three-vertex two-color path is structurally consistent but cannot fit any block when N=M=4,l=2; retaining the structural definition preserves the full algebraic pattern domain
--   - encoding: identities of rational functions → real evaluations with l nonzero and D_q nonzero; grid nonvanishing is concluded eventually in the small-query range; reason: division at a pole is undefined in the source; Lean totalized division is never used to certify an identity there
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Proposition 3.13, PDF = printed page 18. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
open Finset

theorem proposition_3_13 : ∃ Cdeg c₀ : ℝ, 0 < Cdeg ∧ 0 < c₀ ∧ UniformGapVanishing c₀ ∧
    (∀ N k w q : ℕ, ∀ E : Encoding (Fin N × Bool) k,
      ∀ A : Algorithm (Address N 3) k w q,
      ∀ out : (Address N 3 × Bits k) × Fin w → Bool,
      ∃ H : Bivariate, (H.totalDegree : ℝ) ≤ Cdeg * DegreeScale q ∧
        ∀ M l : ℕ, Grid N M l → Eval (Denominator q) M l ≠ 0 →
          FeasibleGap E A out M l =
            l * Eval H M l / Eval (Denominator q) M l + GapError E A out M l) ∧
    (∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ q : ℕ, (q : ℝ) ≤ c₀ * LowerBoundScale N →
      ∀ M l : ℕ, Grid N M l → Eval (Denominator q) M l ≠ 0) := by sorry

end QuantumBipartiteTesting.Bipartiteness
