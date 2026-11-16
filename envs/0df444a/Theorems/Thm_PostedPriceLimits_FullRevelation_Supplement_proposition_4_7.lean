-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_Supplement_proposition_4_7
-- name    : PostedPriceLimits.FullRevelation.Supplement.proposition_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:10:58.374702+00:00
-- url     : https://prove2.me/theorems/24fcce82-9fa1-4d12-9f88-e472ba845a49
-- title:
--   Proposition 4.7 — simultaneous empirical-price concentration
-- statement:
--   Use the §4 random private-label assignment, independent uniform offsets and the complete biased clause families. For every deterministic single-query mechanism in the fixed-order analysis, let $\mathcal E$ be the event of Definition 4.6, simultaneously over every visit and every pair of nonempty indistinguishable unions of whole fibres. For all sufficiently large $n$, uniformly over the mechanism,
--
--   $$\Pr[\mathcal E]\ge1-\lambda^{-2}.$$
--
--   The prices tested are those actually posted from the observed history, and the CDF deviation in $\mathcal E$ is $\lambda^{-4}$. The event is measurable as usual. This is the concentration support for Theorem 2.1; it is not a condition imposed on arbitrary price vectors.
--
--   **Formalization Note** The source fixes deterministic visiting order after Observation 4.1; only this support uses that reduction's fixed-order setting. The final theorem retains the full randomized adaptive-order class. The deterministic biased oracle uses Proposition 3.8's lexicographic simulation tie rule.
--
--   Differences from the source:
--   - encoding: one-based finite items, bidders and ranks in the §4 distribution → zero-based Fin items and bidders, rank values increased by one, and integer roles shifted by kappa; reason: finite relabellings preserve every source instance and the order of indicator vectors
--   - encoding: for sufficiently large n throughout section 4 → an existential integer threshold N at least one before the universal mechanism quantifiers; reason: makes the absolute threshold uniform over all mechanisms
--   - encoding: probabilities of events under the usual measurability convention → explicit MeasurableSet hypothesis for the stated event; reason: makes the source probability convention explicit without assuming any event has large probability
--   - encoding: a fixed deterministic biased-clause tie rule chosen for the Proposition 3.8 reduction → the supporting list minimizes its simulated ordinary additive clause in lexicographic order; reason: fixes the source-permitted simulation rule without exposing the private list or replacing the ordinary lexicographic oracle
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Proposition 4.7, p.10 (PDF 11); section 4 standing assumptions, pp.8–9 (PDF 9–10)

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Supplement_Analysis

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace PostedPriceLimits.FullRevelation.Supplement

/-- Proposition 4.7, with the section's absolute sufficiently-large-n convention. -/
theorem proposition_4_7 :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ M : DetSQ n (itemCount n), FixedOrder M →
      MeasurableSet (priceEvent M) →
      ENNReal.ofReal (1 - (lam n : ℝ)⁻¹ ^ 2) ≤ drawLaw n (priceEvent M) := by sorry

end PostedPriceLimits.FullRevelation.Supplement
