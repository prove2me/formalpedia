-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_Supplement_lemma_4_12
-- name    : PostedPriceLimits.FullRevelation.Supplement.lemma_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:12:47.941928+00:00
-- url     : https://prove2.me/theorems/b9dd4b18-7644-40f5-bdb8-807d7211e666
-- title:
--   Lemma 4.12 — owner affordability versus stealing from every later owner
-- statement:
--   Use the full §4 instance, a deterministic mechanism in the fixed-order analysis, and offsets in $[0,1]$. Suppose the entire event $G$ of Proposition 4.9 holds. At visit $i$, let $f_i(k)$ be the strictly affordable fraction of $Z_{i,k}$ at value $\beta^{1/2}\operatorname{val}(k)$, set to zero for a sample bidder. Let $g_{i,j}(k)=|S_i\cap Z_{j,k}|/|Z_{i,k}|$, with $S_i=\varnothing$ for a sample bidder. For every visit $i$ and every later owner $j>i$,
--
--   $$\sum_{k=1}^{\kappa}f_i(k)\le2\sum_{k=1}^{\kappa}g_{i,j}(k)+\kappa^{2/3}.$$
--
--   The denominator is the current owner's core rank size; these sizes are equal across owners and positive. This is a deterministic implication on the full response-matrix event, including $\mathcal E$. It supplies the stealing comparison needed for Theorem 2.1.
--
--   Differences from the source:
--   - encoding: one-based finite items, bidders and ranks in the §4 distribution → zero-based Fin items and bidders, rank values increased by one, and integer roles shifted by kappa; reason: finite relabellings preserve every source instance and the order of indicator vectors
--   - encoding: for sufficiently large n throughout section 4 → an existential integer threshold N at least one before the universal mechanism quantifiers; reason: makes the absolute threshold uniform over all mechanisms
--   - encoding: a fixed deterministic biased-clause tie rule chosen for the Proposition 3.8 reduction → the supporting list minimizes its simulated ordinary additive clause in lexicographic order; reason: fixes the source-permitted simulation rule without exposing the private list or replacing the ordinary lexicographic oracle
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Lemma 4.12, p.14 (PDF 15); section 4 standing assumptions, pp.8–9 (PDF 9–10)

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Supplement_Analysis

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace PostedPriceLimits.FullRevelation.Supplement

/-- Lemma 4.12: retain all later owners, the factor 2 and kappa^(2/3). -/
theorem lemma_4_12 :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ M : DetSQ n (itemCount n), FixedOrder M →
      ∀ ω : Draw n, (∀ i, 0 ≤ ω.2 i ∧ ω.2 i ≤ 1) → ω ∈ matrixEvent M →
      ∀ i j : Fin n, i < j →
        ∑ k : Rank n, f ω M i k ≤ 2 * ∑ k : Rank n, g ω M i j k +
          (kappa n : ℝ) ^ (2 / 3 : ℝ) := by sorry

end PostedPriceLimits.FullRevelation.Supplement
