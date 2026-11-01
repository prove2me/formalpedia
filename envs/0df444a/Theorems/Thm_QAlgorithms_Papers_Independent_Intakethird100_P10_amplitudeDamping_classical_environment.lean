-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_amplitudeDamping_classical_environment
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.amplitudeDamping_classical_environment
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:42:42.550205+00:00
-- url     : https://prove2.me/theorems/5e70a405-52d7-44e3-9bf1-ef3fea37e0c2
-- title:
--   Amplitude-damping complement has commuting basis outputs
-- statement:
--   Let $0\le\gamma\le1$ be the original amplitude-damping probability. Its printed complementary map is the linear map with diagonal entries $\rho_{00}+(1-\gamma)\rho_{11}$ and $\gamma\rho_{11}$, and off-diagonal entries $\sqrt\gamma\rho_{01}$ and $\sqrt\gamma\rho_{10}$. On the computational-basis states,
--
--   $$
--   W^*(|0\rangle\langle0|)=|0\rangle\langle0|,\qquad
--   W^*(|1\rangle\langle1|)=(1-\gamma)|0\rangle\langle0|+\gamma|1\rangle\langle1|.
--   $$
--
--   The two outputs commute. This supplies the classical-environment criterion for the specified basis; no all-parameter degradability claim is made.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 11, Appendix B, unnumbered amplitude-damping classical-environment example

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF pp.10–11, Appendix B: the two amplitude-damping complement outputs,
and their commutation, for every damping parameter in [0,1]. No degradability claim. -/
theorem amplitudeDamping_classical_environment (gamma : ℝ) (hlo : 0 ≤ gamma) (hhi : gamma ≤ 1) :
    amplitudeComplement gamma (basisDensity false) = basisDensity false ∧
    amplitudeComplement gamma (basisDensity true) =
      ((1 - gamma : ℝ) : ℂ) • basisDensity false + (gamma : ℂ) • basisDensity true ∧
    Commute (amplitudeComplement gamma (basisDensity false))
      (amplitudeComplement gamma (basisDensity true)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end
