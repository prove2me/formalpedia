-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_covariantZeroFrequency
-- name    : QAlgorithms.Papers.Independent.Information100.P44.covariantZeroFrequency
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:46:02.473025+00:00
-- url     : https://prove2.me/theorems/f0f01a36-6d68-490a-ae61-df35a55245d0
-- title:
--   IV C: nontrivial polygon transfers lie at zero frequency
-- statement:
--   Let $\Phi$ be a complex-linear time-translation covariant map on a nonzero finite system with basis energies $E_i$. No positivity, trace preservation, or Gibbs condition is assumed. Then
--   $$E_i\ne E_j\ \Longrightarrow\ \Phi(|i\rangle\langle j|)_{rr}=0\quad\text{for every }r,$$
--   $$E_r\ne E_s\ \Longrightarrow\ \Phi(|i\rangle\langle i|)_{rs}=0\quad\text{for every }i.$$
--   These frequency-selection identities locate nontrivial covariant polygon applications in degenerate zero-frequency sectors.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 15, IV C: nontrivial polygon transfers lie at zero frequency

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.15, Eqs.(107),(109): covariance alone for linear maps gives both zero-frequency rules. -/
theorem covariantZeroFrequency {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ)
    (Phi : Map d) (hlin : IsComplexLinear Phi) (hcov : IsCovariant E Phi) :
    (∀ i j, E i ≠ E j → ∀ r, Phi (matrixUnit i j) r r = 0) ∧
    (∀ r s, E r ≠ E s → ∀ i, Phi (matrixUnit i i) r s = 0) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
