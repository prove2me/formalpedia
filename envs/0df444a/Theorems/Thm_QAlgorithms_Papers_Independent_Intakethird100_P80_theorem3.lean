-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P80_theorem3
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P80.theorem3
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:24:21.617216+00:00
-- url     : https://prove2.me/theorems/604bcd9f-490e-410a-95eb-9fd705abd729
-- title:
--   Correlated and product games: all equalizer conclusions
-- statement:
--   Fix a proper quantum experiment with two parties, two settings each, and arbitrary nonempty finite outcome alphabets. Write $U$ for its KL payoff, $\Sigma$ for all setting laws, and $\Sigma_{\rm UC}$ for product setting laws. There is a finite $V>0$ and a correlated saddle point of value $V$, and
--
--   $$\sup_{\Sigma_{\rm UC}}\inf_\Pi U\le\sup_\Sigma\inf_\Pi U=V,\qquad\inf_\Pi\sup_{\Sigma_{\rm UC}}U=\inf_\Pi\sup_\Sigma U=V.$$
--
--   The set of local minimax strategies is nonempty and is the same for both games. Every such strategy $\pi$ is an equalizer: $U(\sigma,\pi)=V$ for every $\sigma\in\Sigma$.
--
--   The product-setting game has a saddle point if and only if there exist a product law $\sigma^*$ and a local law $\pi^*$ such that $\pi^*$ minimizes $U(\sigma^*,\cdot)$ and is an equalizer against all setting laws. Every pair with these properties is a saddle point.
--
--   This characterizes when the product game admits a saddle without assuming its maximin equals $V$ in general. Saddle inequalities agree with Definition 4 on PDF p.13 and the proof on p.35.
-- source:
--   The statistical strength of nonlocality proofs, arXiv:quant-ph/0307125v2, PDF p. 14, Theorem 3: all correlated/uncorrelated and equalizer conclusions

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P80

open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Filter

/-- PDF p.14, Theorem 3, all parts; pp.35–36: arbitrary finite outcomes are retained.
No equality between the product MAXIMIN and V is asserted without a saddle hypothesis. -/
theorem theorem3 {S : BellExperiment} (hS : TwoByTwo S) (Q : Table S)
    (hQ : NonlocalityProof Q) (hproper : Proper Q) :
    ∃ V : ℝ≥0∞, 0 < V ∧ V < ⊤ ∧
      (∃ (s : Sigma S) (p : PiLocal S),
        Saddle Q (stdSimplex ℝ (Settings S)) s.1 p.1 ∧ statisticalPayoff Q s.1 p.1 = V) ∧
      uncorrelatedStrength Q ≤ correlatedStrength Q ∧ correlatedStrength Q = V ∧
      minimax Q (productSettings S) = V ∧ minimax Q (stdSimplex ℝ (Settings S)) = V ∧
      (minimizers Q (stdSimplex ℝ (Settings S))).Nonempty ∧
      minimizers Q (stdSimplex ℝ (Settings S)) = minimizers Q (productSettings S) ∧
      (∀ p ∈ minimizers Q (stdSimplex ℝ (Settings S)),
        ∀ s : Sigma S, statisticalPayoff Q s.1 p = V) ∧
      ((∃ (s : Sigma S) (p : PiLocal S), Saddle Q (productSettings S) s.1 p.1) ↔
        ∃ (s : Sigma S) (p : PiLocal S), Uncorrelated s.1 ∧
          statisticalPayoff Q s.1 p.1 = lowerValue Q s.1 ∧ Equalizer Q p.1) ∧
      (∀ (s : Sigma S) (p : PiLocal S), Uncorrelated s.1 →
        statisticalPayoff Q s.1 p.1 = lowerValue Q s.1 → Equalizer Q p.1 →
        Saddle Q (productSettings S) s.1 p.1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P80

end
