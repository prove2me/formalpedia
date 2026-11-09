-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_all_query_circuit
-- name    : SubsetSumPartialMatch.SubsetSum.all_query_circuit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:27.154146+00:00
-- url     : https://prove2.me/theorems/97026b6f-e491-479b-923f-afe43809a5dc
-- title:
--   Theorem 3.8 — all-query circuit degree profiles
-- statement:
--   Let $a,b\in\mathbb R$ satisfy $a>0$ and $4a\le1-b\le1/2$, and assume $\kappa>4a$. Then for every sufficiently large even $k$ there is a colored EXACT$_\mathbb Z$ circuit $C_k$ computing $P_{k,1/2}$ with at most $(k+1)^2$ colors, each of which is a pair $(\mu,\theta)$ with $a\le\mu\le2a$ and $\mu\le\theta\le2\mu$. Moreover, for every color, writing $C'=(C_k)_{(\mu,\theta)}$,
--   $$\deg_L(C')\le2^{(V_L(\mu,\theta)+o(1))k},\qquad\deg_R(C')\le2^{(V_R(\mu,\theta)+o(1))k},$$
--   where the $o(1)$ terms are uniform over all colors.
--
--   This gives a single circuit for all queries, with a separate degree profile for each color class.
--
--   Differences from the source:
--   - encoding: $o(1)$ uniform over colors, for every sufficiently large even $k$ → one function $\mathrm{err}(k)\to0$ and a threshold $N$, chosen before $k$ and the colors; reason: this is the meaning of a uniform $o(1)$
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 24, Theorem 3.8 (statement continues on p. 25)

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Circuit
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Entropy

namespace SubsetSumPartialMatch.SubsetSum

/-- Theorem 3.8. Let `a > 0`, `4a ≤ 1 - b ≤ 1/2` and `κ > 4a`. For every sufficiently large even `k`
there is a colored EXACT_Z circuit `C_k` for `P_{k,1/2}` with at most `(k+1)²` colors, each a pair
`(µ, θ)` with `a ≤ µ ≤ 2a`, `µ ≤ θ ≤ 2µ`, such that for every color the color class has degrees at
most `2^{(V_L(µ,θ)+o(1))k}` and `2^{(V_R(µ,θ)+o(1))k}`, the `o(1)` being uniform over colors. -/
theorem all_query_circuit {a b : ℝ} (ha : 0 < a) (hab : 4 * a ≤ 1 - b) (hb : 1 - b ≤ 1 / 2)
    (hκ : 4 * a < kappa a b) :
    ∃ (err : ℕ → ℝ) (N : ℕ), Filter.Tendsto err Filter.atTop (nhds 0) ∧
      ∀ k ≥ N, Even k →
        ∃ C : ColoredCircuit (BinStr k) (PMCol k (1 / 2)) (ℝ × ℝ),
          C.toLinCircuit.Computes (pm k (1 / 2)) ∧ C.colors.card ≤ (k + 1) ^ 2 ∧
          ∀ ζ ∈ C.colors, ζ ∈ colorDomain a ∧
            ((C.part ζ).degL : ℝ) ≤ (2 : ℝ) ^ ((VL a b ζ.1 ζ.2 + err k) * k) ∧
            ((C.part ζ).degR : ℝ) ≤ (2 : ℝ) ^ ((VR a b ζ.1 ζ.2 + err k) * k) := by sorry

end SubsetSumPartialMatch.SubsetSum
