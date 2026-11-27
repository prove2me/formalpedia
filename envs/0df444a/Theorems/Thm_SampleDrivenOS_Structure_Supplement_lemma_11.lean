-- Prove2me | Theorems.Thm_SampleDrivenOS_Structure_Supplement_lemma_11
-- name    : SampleDrivenOS.Structure.Supplement.lemma_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:49:31.512615+00:00
-- url     : https://prove2.me/theorems/398af7a3-2e34-400e-9173-a82aa6fd8a26
-- title:
--   Lemma 11 — limiting selection probability of a fixed global rank
-- statement:
--   Fix 0≤p<1, a nondecreasing feasible threshold sequence t, and a positive global rank j. The threshold algorithm sees each finite prefix of the same ranked population through independent uniform arrival times. For any weight instance consistent with that ranking,
--   $$
--   \lim_{N\to\infty}\Pr(\operatorname{ALG}_t(Y_{[N]})\text{ selects global rank }j)
--   =\sum_{i=1}^{\infty}\int_{t_i}^{t_{i+1}}\sum_{\ell=1}^{\min(j,i)}
--   \frac{T_i}{\tau^i}\binom{j-1}{\ell-1}(1-\tau)^{j-\ell}\tau^{\ell-1}\,d\tau.
--   $$
--   Here T_i is the product of t₁,…,t_i. Each displayed integral is integrable and the series of integral terms is summable; both properties are included as conclusions. The formula includes all positive i and all relative ranks up to min(j,i).
--
--   This identifies individual global-rank probabilities for the finite-to-continuous bridge, independently of the numerical values or their ties.
--
--   Differences from the source:
--   - reading: ALG_t(Y_[N])=Y_j → selection of the item with fixed global rank j; reason: the universal tie-break of §2.1 and §5 fixes identities even when numerical weights coincide
--   - encoding: N→∞ and sum over i≥1 → N+1→∞ and a tsum indexed by i+1, with integrability and summability conclusions; reason: positive population sizes and the full series are retained; convergence is asserted rather than assumed
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 18, Lemma 11

import Definitions.Def_SampleDrivenOS_Structure_Supplement_Thresholds

open MeasureTheory Filter
open scoped Topology

namespace SampleDrivenOS.Structure.Supplement

theorem lemma_11 (p : ℝ) (hp : 0 ≤ p ∧ p < 1) (t : ℕ → ℝ)
    (ht : IsThresholds p t) (j : ℕ) (hj : 1 ≤ j) :
    (∀ i : ℕ, 1 ≤ i → IntervalIntegrable (rankLimitIntegrand t j i) volume (t i) (t (i + 1))) ∧
    Summable (fun i : ℕ => rankLimitTerm t j (i + 1)) ∧
    Tendsto (fun N : ℕ => selectionProbability (N + 1) p t j) atTop
      (𝓝 (∑' i : ℕ, rankLimitTerm t j (i + 1))) := by sorry

end SampleDrivenOS.Structure.Supplement
