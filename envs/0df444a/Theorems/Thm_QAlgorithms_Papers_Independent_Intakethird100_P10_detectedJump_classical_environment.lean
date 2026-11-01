-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_detectedJump_classical_environment
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.detectedJump_classical_environment
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:43:19.343942+00:00
-- url     : https://prove2.me/theorems/b5b59e23-15a3-4b1d-bfa2-bc49bde58636
-- title:
--   Detected-jump complement has commuting basis outputs
-- statement:
--   For $0\le\gamma\le1$, use the photon-detected-jump complementary map printed in Appendix B, extended linearly as $\rho\mapsto\operatorname{diag}(\operatorname{Tr}\rho-\gamma\rho_{11},\gamma\rho_{11})$. Its computational-basis outputs satisfy
--
--   $$
--   W^*(|0\rangle\langle0|)=|0\rangle\langle0|,\qquad
--   W^*(|1\rangle\langle1|)=(1-\gamma)|0\rangle\langle0|+\gamma|1\rangle\langle1|,
--   $$
--
--   and therefore commute. This verifies the stated basis criterion using the cited complement, with no full-Fock or capacity assertion.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 11, Appendix B, unnumbered photon-detected-jump classical-environment example

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF p.11, Appendix B: computational-basis outputs of the printed detected-jump
complement commute. The map does not describe a full-Fock photonic protocol. -/
theorem detectedJump_classical_environment (gamma : ℝ) (hlo : 0 ≤ gamma) (hhi : gamma ≤ 1) :
    detectedJumpComplement gamma (basisDensity false) = basisDensity false ∧
    detectedJumpComplement gamma (basisDensity true) =
      ((1 - gamma : ℝ) : ℂ) • basisDensity false + (gamma : ℂ) • basisDensity true ∧
    Commute (detectedJumpComplement gamma (basisDensity false))
      (detectedJumpComplement gamma (basisDensity true)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end
