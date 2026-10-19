-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_shellGibbsStochastic
-- name    : QAlgorithms.Papers.Independent.Information100.P44.shellGibbsStochastic
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:33:25.314296+00:00
-- url     : https://prove2.me/theorems/b68781c5-f266-410d-8395-41ef2f393fb1
-- title:
--   Corollary 2: Gibbs-stochastic shell transition matrix
-- statement:
--   For any finite-bath thermal dilation at real inverse temperature $\beta$, let $w_{r|i}$ be its common shell vectors, and let $\gamma_i=e^{-\beta E_i}/\sum_j e^{-\beta E_j}$ be the Gibbs weight of basis state $i$. Then
--   $$\sum_r\|w_{r|i}\|^2=1\quad\text{for every }i,\qquad \sum_i\|w_{r|i}\|^2\gamma_i=\gamma_r\quad\text{for every }r.$$
--   Thus the shell transition matrix is column-stochastic and Gibbs-stationary. Degeneracy labels remain separate basis labels.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 8, Corollary 2: Gibbs-stochastic shell transition matrix

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.8, Corollary 2: column stochasticity and per-basis Gibbs stationarity. -/
theorem shellGibbsStochastic {d b : ℕ} (hd : 0 < d) (E : Fin d → ℝ)
    (beta : ℝ) (D : ThermalDilation E beta b) :
    (∀ i, (∑ r, ‖shellVector D r i‖ ^ 2) = 1) ∧
    (∀ r, (∑ i, ‖shellVector D r i‖ ^ 2 * gibbsWeight E beta i) = gibbsWeight E beta r) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
