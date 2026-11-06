-- Prove2me | Theorems.Thm_SparseMatchingDesign_theorem_3_ring_loss_le
-- name    : SparseMatchingDesign.theorem_3_ring_loss_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:18:52.923142+00:00
-- url     : https://prove2.me/theorems/143336eb-9c4b-41d0-9689-3d789d3d55c2
-- title:
--   Theorem 3 — $L(R_{n,K})\le\frac{3n}{d+1}q^{(d+1)/3}=3ne^{-\gamma_2(d+1)-\log(d+1)}$
-- statement:
--   Let $K\ge1$ divide $n$, let the node survival probability be $p\in(0,1)$ with $q=1-p$, and let $d=3K-1$ be the density of the $K$-ring. The matching loss of $R_{n,K}$ against the complete input graph $K_n$ satisfies
--   $$L(R_{n,K})\le\frac{3n}{d+1}\,q^{(d+1)/3}=3n\,e^{-\gamma_2(d+1)-\log(d+1)},\qquad \gamma_2=\tfrac13\log\!\big(\tfrac1q\big).$$
--   The loss of the $K$-ring decays exponentially in its density, whereas that of the $K$-cluster decays only like $n/(d+1)$ (Theorem 2); with the lower bound of Theorem 1 this makes $K$-rings order-optimal sparse designs.
--
--   Differences from the source:
--   - reading: d, the density of R_{n,K}, which the paper fixes as d = 3K − 1 (p.19, footnote 5, and p.ec8 "the facts that d = 3K − 1") → d := 3K − 1, written (3 * K - 1 : ℝ); reason: the paper's stated value; the actual density min{3K − 1, n − 1} differs only when n/K ∈ {1, 2}, where R_{n,K} = Kₙ and L = 0, and there 3K − 1 gives the smaller, so stronger, bound
--   - encoding: G^in = Kₙ (§5) → matchingLoss p ⊤ (kRing n K); reason: ⊤ is the complete graph
--   - encoding: p ∈ (0,1) (§2.2, p.6) → hypotheses 0 < p and p < 1; reason: the paper's standing assumption
--   - encoding: expectation over the random surviving set → finite sum over subsets weighted by p^{|S|}(1 − p)^{n − |S|}; reason: same distribution
--   - encoding: standing assumptions K, m ∈ ℕ with n = Km (§2.1) and n a multiple of K (footnote 5, p.19) → hypotheses 0 < K and K ∣ n; reason: the paper's convention, written into the binders
--   - encoding: nodes [n], clusters ⌈i/K⌉ ∈ [n/K], the K-ring of eq. (6) → Fin n with paper node i = index i − 1, 0-based clusters i / K, eq. (6) applied to both orders of a pair; reason: a relabelling; same graphs
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §5.3, Theorem 3, p.19 (pdf p.19); d = 3K − 1: p.19 line 1 and footnote 5

import Mathlib
import Definitions.Def_SparseMatchingDesign_matchingLoss
import Definitions.Def_SparseMatchingDesign_kRing

namespace SparseMatchingDesign

/-- **Theorem 3.** For the `K`-ring `R_{n,K}` with density `d = 3K − 1`, node survival
probability `p ∈ (0,1)` and `q = 1 − p`,
`L(R_{n,K}) ≤ 3n/(d+1) · q^{(d+1)/3} = 3n e^{−γ₂(d+1) − log(d+1)}`, where `γ₂ = (1/3) log(1/q)`.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §5.3, Theorem 3, p.19: "L(R_{n,K}) ≤ 3n/(d+1) q^{(d+1)/3} = 3n e^{−γ₂(d+1)−log(d+1)}, where
γ₂ = 1/3 log(1/q)." Also p.19, first line: "For each fixed n, there is a one-to-one correspondence
between K and its density d = 3K − 1", and footnote 5: "we always assume that n is a multiple of
K".

**Formalization Note** The loss is against the complete input graph `G^in = Kₙ = ⊤` (§5). `d` is
the paper's `d = 3K − 1` (p.19, footnote 5, and p.ec8 "the facts that d = 3K − 1"), written
`(3 * K - 1 : ℝ)`. `q^{(d+1)/3}` is a real power. `K ≥ 1`, `K ∣ n` (footnote 5) and
`0 < p < 1` (§2.2, p.6) are hypotheses. Both the inequality and the equality are stated. -/
theorem theorem_3_ring_loss_le (n K : ℕ) (hK : 0 < K) (hKn : K ∣ n) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) :
    matchingLoss p ⊤ (kRing n K) ≤
        3 * (n : ℝ) / ((3 * K - 1 : ℝ) + 1) * (1 - p) ^ (((3 * K - 1 : ℝ) + 1) / 3) ∧
    3 * (n : ℝ) / ((3 * K - 1 : ℝ) + 1) * (1 - p) ^ (((3 * K - 1 : ℝ) + 1) / 3) =
        3 * (n : ℝ) * Real.exp (-((1 / 3) * Real.log (1 / (1 - p))) * ((3 * K - 1 : ℝ) + 1) -
          Real.log ((3 * K - 1 : ℝ) + 1)) := by sorry

end SparseMatchingDesign
