-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_chsh_endpoint_costs
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.chsh_endpoint_costs
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:49:13.003167+00:00
-- url     : https://prove2.me/theorems/0292a859-8f73-49fe-bc10-c260cdf19bc7
-- title:
--   Appendix C unnumbered: endpoint tightness
-- statement:
--   Use the normalized binary CHSH law with uniform independent inputs and bias $\beta$, so its winning probability is $(1+\beta)/2$. Let $\mathcal R^q_\beta$ be the entanglement-assisted one-way simulation rates with message entropy cost and vanishing full-law error. The least achievable rates at the stated endpoints are
--
--   $$
--   \min\mathcal R^q_1=1,\qquad
--   \min\mathcal R^q_\beta=0\quad(0\le\beta\le1/\sqrt2).
--   $$
--
--   These are attained endpoint costs. They combine the lower bound with the one-bit strategy at bias one and the zero-communication realizations in the quantum range. No equality at intermediate biases above $1/\sqrt2$ is claimed.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 26, Appendix C unnumbered: endpoint tightness

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- Appendix C, PDF pp.24,26: exact endpoint costs, including the zero-cost realizable
range. No intermediate-bias saturation is asserted. -/
theorem chsh_endpoint_costs :
    (∀ p : Law (Fin 2 × Fin 2 × Fin 2 × Fin 2), IsCHSHLaw 1 p → IsLeast (quantumRates p) 1) ∧
    (∀ bias : ℝ, 0 ≤ bias → bias ≤ 1 / Real.sqrt 2 →
      ∀ p : Law (Fin 2 × Fin 2 × Fin 2 × Fin 2), IsCHSHLaw bias p → IsLeast (quantumRates p) 0) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
