-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_Supplement_proposition_4_9
-- name    : PostedPriceLimits.FullRevelation.Supplement.proposition_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:11:43.613099+00:00
-- url     : https://prove2.me/theorems/c6e332ec-07df-4774-9d43-f65384cbf3af
-- title:
--   Proposition 4.9 — common response matrix and bounded information depth
-- statement:
--   Under the same full §4 distribution and deterministic fixed-order mechanism, the following conjunction holds with probability at least $1-\lambda^{-1}$ for all sufficiently large $n$, uniformly over the mechanism:
--
--   1. $\mathcal E$ holds.
--   2. Simultaneously before every visit $i$, all items in $X_{i,K}$ are indistinguishable for every $K\in\mathcal K_{i-1}$.
--   3. Whenever the utility-maximizing set at that visit is nonempty, there exists one matrix $A_i^*\in\mathcal A$ with $s(A_i^*)\le i-1$, and the returned clause list uses $A_\sigma=A_i^*$ on every $i$-relevant slice.
--
--   Equivalently, for the complete conjunction $G$ just defined,
--
--   $$\Pr[G]\ge1-\lambda^{-1}.$$
--
--   The single event includes both conclusions for all visits, with no conditioning or separate per-visit guarantee. Empty demand returns zero. This statement controls the information carried by oracle responses in the proof of Theorem 2.1. Its probability uses the usual measurability convention.
--
--   **Formalization Note** Internal matrix indices are not added to the mechanism's observations; histories retain only the returned coefficients. The tie rule implements the ordinary lexicographic oracle simulation of Proposition 3.8.
--
--   Differences from the source:
--   - encoding: one-based finite items, bidders and ranks in the §4 distribution → zero-based Fin items and bidders, rank values increased by one, and integer roles shifted by kappa; reason: finite relabellings preserve every source instance and the order of indicator vectors
--   - encoding: for sufficiently large n throughout section 4 → an existential integer threshold N at least one before the universal mechanism quantifiers; reason: makes the absolute threshold uniform over all mechanisms
--   - encoding: probabilities of events under the usual measurability convention → explicit MeasurableSet hypothesis for the stated event; reason: makes the source probability convention explicit without assuming any event has large probability
--   - encoding: a fixed deterministic biased-clause tie rule chosen for the Proposition 3.8 reduction → the supporting list minimizes its simulated ordinary additive clause in lexicographic order; reason: fixes the source-permitted simulation rule without exposing the private list or replacing the ordinary lexicographic oracle
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Proposition 4.9, p.11 (PDF 12); section 4 standing assumptions, pp.8–9 (PDF 9–10)

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Supplement_Analysis

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace PostedPriceLimits.FullRevelation.Supplement

/-- Proposition 4.9: one simultaneous event, including E and both clauses. -/
theorem proposition_4_9 :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ M : DetSQ n (itemCount n), FixedOrder M →
      MeasurableSet (matrixEvent M) →
      ENNReal.ofReal (1 - (lam n : ℝ)⁻¹) ≤ drawLaw n (matrixEvent M) := by sorry

end PostedPriceLimits.FullRevelation.Supplement
