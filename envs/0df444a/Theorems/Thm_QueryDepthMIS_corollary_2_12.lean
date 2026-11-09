-- Prove2me | Theorems.Thm_QueryDepthMIS_corollary_2_12
-- name    : QueryDepthMIS.corollary_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:36:36.508338+00:00
-- url     : https://prove2.me/theorems/52eb7990-1acc-4368-bf62-0e2db2b51eda
-- title:
--   Corollary 2.12 — $\Pr[Z(\pi) > n^9] \le 1/n^7$
-- statement:
--   Let $G$ be a simple graph on $n \ge 2$ vertices and $\pi$ a uniformly random permutation of $V$. Then
--   $$
--   \Pr\big[Z(\pi) > n^9\big] \le \frac{1}{n^7}.
--   $$
--
--   Differences from the source:
--   - encoding: a uniformly random permutation π of V, π(i) the i-th vertex → the uniform (counting) law on orderings ω : V ≃ Fin n, π = ω⁻¹, with 1-based ranks rank ω v = ω v + 1; reason: the same law; positions keep the paper's 1-based values
--   - encoding: a simple graph G with no order on V → an additional instance [LinearOrder V]; reason: required by the reused RGMISFast.tau to break rank ties; ranks of a permutation are injective, so it never acts
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Corollary 2.12, p.10

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_QueryDepthMIS_Z
import Definitions.Def_QueryDepthMIS_rank

set_option autoImplicit false

namespace QueryDepthMIS

/-- Corollary 2.12 (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Corollary 2.12, p.10): "For a uniformly random permutation π on V,
Pr[Z(π) > n⁹] ≤ 1/n⁷."

For every simple graph `G` on `n ≥ 2` vertices, the probability that the total number of query
paths exceeds `n⁹` is at most `1/n⁷`.

**Formalization Note** `n ≥ 2` is the standing assumption of §2.1, p.7. -/
theorem corollary_2_12 :
    ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      2 ≤ Fintype.card V →
      PunctSketch.coinProb (fun ω : Perm V => Fintype.card V ^ 9 < Z G (rank ω)) ≤
        1 / (Fintype.card V : ℝ) ^ 7 := by sorry

end QueryDepthMIS
