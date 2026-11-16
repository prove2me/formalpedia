-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_lemma_5_1
-- name    : SampleCRS.AlmostGreedy.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:41:44.033877+00:00
-- url     : https://prove2.me/theorems/791014cc-a5d5-4a15-bdff-7c05563be379
-- title:
--   Lemma 5.1 — uniform acceptance-tail and moving-prefix limits
-- statement:
--   Fix $k\ge2$ and the optimal known-probability adversarial balance $\gamma=\gamma_{\rm adv}(k)$. Consider any sequence of instances, with possibly varying sizes and policies, satisfying $p_i^{(r)}>0$, $\sum_i p_i^{(r)}=k$ and $\delta_r=\max_i p_i^{(r)}\to0$. Each policy is $\gamma$-balanced on its instance and may have full distributional knowledge. Let $N_j^{(r)}$ be its number of acceptances in the first $j$ arrivals, and interpolate $H_{2,j}^{(r)}=E[(N_j^{(r)}-1)^+]$ linearly at the prefix masses $s_j^{(r)}$.
--
--   With $h_2$ defined by (11),
--   $$H_2^{(\delta_r)}\longrightarrow h_2\quad\text{uniformly on }[0,k].$$
--   Moreover, for every sequence $j_r\le n_r$ and every real $t$ with $s_{j_r}^{(r)}\to t$,
--   $$E[(N_{j_r}^{(r)}-1)^+]\longrightarrow h_2(t).$$
--   This includes every moving-prefix limit, not just the two-block constructions used later. The balance assumption need only hold at each indicated instance, as in the proof in Appendix A.5.
--
--   Differences from the source:
--   - encoding: arbitrary randomized nonanticipating policies, even with fixed order known in advance → real behavioral kernels on complete activation/action histories in arrival-position labels; reason: perfect recall on the finite observation tree represents arbitrary independent private randomness; relabelling a known order preserves all information
--   - encoding: positive-bias instances, interpolation and h₂ in (11) → dependent finite sizes, half-open affine segments, the actual terminal node and explicit hSecond; reason: strictly positive p gives distinct interpolation nodes; hSecond is exactly formula (11) with the operational optimum
--   - generalization: a sequence of γ-balanced OCRSs and instances → arbitrary kernels with γ balance at their indicated instances; reason: Appendix A.5 uses only the acceptance inequalities at each indicated instance; every globally γ-balanced scheme specializes to these kernels
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Lemma 5.1, p. 24

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_prefixLimits

namespace SampleCRS.AlmostGreedy.Supplement

/-- Lemma 5.1, p.24. uniform acceptance-tail and moving-prefix limits. -/
theorem lemma_5_1 (k : ℕ) (hk : 2 ≤ k) (n : ℕ → ℕ)
    (p : (r : ℕ) → Fin (n r) → ℝ) (π : (r : ℕ) → OnlineKernel (n r))
    (hp : ∀ r, ValidProb (p r)) (hpos : ∀ r i, 0 < p r i)
    (hmass : ∀ r, (∑ i, p r i) = (k : ℝ))
    (hbal : ∀ r, BalancedInstance k (gammaAdv k) (π r) (p r))
    (hsmall : Filter.Tendsto (fun r => maxBias (p r)) Filter.atTop (nhds 0)) :
    TendstoUniformlyOn (fun r t => interpolateTail k (π r) (p r) 2 t)
      (hSecond k) Filter.atTop (Set.Icc 0 (k : ℝ)) ∧
    ∀ j : ℕ → ℕ, (∀ r, j r ≤ n r) → ∀ t : ℝ,
      Filter.Tendsto (fun r => prefixMass (p r) (j r)) Filter.atTop (nhds t) →
      Filter.Tendsto (fun r => tailExpectation k (π r) (p r) 2 (j r))
        Filter.atTop (nhds (hSecond k t)) := by sorry

end SampleCRS.AlmostGreedy.Supplement
