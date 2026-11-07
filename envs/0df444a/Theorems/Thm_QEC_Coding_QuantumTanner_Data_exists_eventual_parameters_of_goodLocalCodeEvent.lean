-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_exists_eventual_parameters_of_goodLocalCodeEvent
-- name    : QEC.Coding.QuantumTanner.Data.exists_eventual_parameters_of_goodLocalCodeEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:02:05.175305+00:00
-- url     : https://prove2.me/theorems/016ccfff-b826-4540-aba0-41378281142f
-- title:
--   Data: exists eventual parameters of good Local Code Event
-- statement:
--   One threshold works for every finite geometry and every successful local
--   draw. No global distance, rate, or minimum-attainment certificate is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SampleParameters.lean#L44-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SampleParameters.lean#L44-L123

import Definitions.Def_QEC_Coding_QuantumTanner_Parameters
import Definitions.Def_QEC_Coding_QuantumTanner_SampleParameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical QEC.Coding.SmallSetExpansion
universe v
open QEC.Coding.QuantumTanner.Data

theorem QEC.Coding.QuantumTanner.Data.exists_eventual_parameters_of_goodLocalCodeEvent
    (delta epsilon gamma rho : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1)
    (hRho : 0 ≤ rho) (hRhoHalf : rho < 1 / 2) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (G A B Square XBasis ZBasis : Type v)
        [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
        [Fintype XBasis] [Fintype ZBasis],
      ∀ (D : Data G A B Square XBasis ZBasis) (r : Nat), 0 < r → r < Delta →
      (r : ℝ) ≤ rho * Delta →
      Fintype.card A = Delta → Fintype.card B = Delta →
      ∀ (sample : RandomLocalCodeSample r A B),
      D.codeA = sample.codeA → D.codeB = sample.codeB →
      GoodLocalCodeEvent r (Delta - r) (Nat.ceil (delta * Delta))
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2)))
        (Nat.floor ((Delta : ℝ) ^ gamma)) sample →
      D.complex.HasCayleyLinkIdentities →
      HasMeanZeroBilinearBound D.complex.leftCayleyGraph (2 * Real.sqrt (Delta : ℝ)) →
      HasMeanZeroBilinearBound D.complex.rightCayleyGraph (2 * Real.sqrt (Delta : ℝ)) →
      0 < D.blockLength ∧ 0 < D.encodedDimension ∧
      ∃ distance : Nat, D.HasParameters D.blockLength D.encodedDimension distance ∧
        (1 - 2 * rho) ^ 2 * D.blockLength ≤ (D.encodedDimension : ℝ) ∧
        delta * D.blockLength / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) ≤
          (distance : ℝ) ∧
        QEC.Coding.BoundedLocality
          (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile
          (Delta * Delta) := by sorry
