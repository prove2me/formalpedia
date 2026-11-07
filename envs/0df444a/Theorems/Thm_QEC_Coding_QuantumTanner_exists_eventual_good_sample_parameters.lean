-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_eventual_good_sample_parameters
-- name    : QEC.Coding.QuantumTanner.exists_eventual_good_sample_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:00:54.678068+00:00
-- url     : https://prove2.me/theorems/4040baae-e0c5-40c1-9192-77c9d02e18c5
-- title:
--   Quantum Tanner: exists eventual good sample parameters
-- statement:
--   Select one matrix draw before the group geometry. On every admissible
--   four-corner geometry whose actual Cayley graphs satisfy the spectral bounds,
--   that same draw gives positive rate, attained global distance, and locality.
--   This does not replace the arithmetic existence proof for those graphs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SampleParameters.lean#L131-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SampleParameters.lean#L131-L200

import Definitions.Def_QEC_Coding_QuantumTanner_Parameters
import Definitions.Def_QEC_Coding_QuantumTanner_SampleParameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical QEC.Coding.SmallSetExpansion
universe v

theorem QEC.Coding.QuantumTanner.exists_eventual_good_sample_parameters
    (delta epsilon gamma rho : ℝ) (hDeltaDistance : 0 < delta)
    (hDeltaHalf : delta < 1 / 2)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
      Fintype.card A = Delta → Fintype.card B = Delta →
      ∃ sample : RandomLocalCodeSample (randomRowCount rho Delta) A B,
        GoodLocalCodeEvent (randomRowCount rho Delta) (Delta - randomRowCount rho Delta)
          (Nat.ceil (delta * Delta))
          (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2)))
          (Nat.floor ((Delta : ℝ) ^ gamma)) sample ∧
        ∀ (G : Type v) [Group G] [Fintype G]
          (L : A → G) (R : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
          (hL : Function.Injective L) (hR : Function.Injective R)
          (hLA : ∀ a, L (invA a) = (L a)⁻¹)
          (hRB : ∀ b, R (invB b) = (R b)⁻¹)
          (hTNC : ∀ g a b, L a * g ≠ g * R b),
        HasMeanZeroBilinearBound
          (cayleySquareComplex L R invA invB hL hR hLA hRB hTNC).leftCayleyGraph
          (2 * Real.sqrt (Delta : ℝ)) →
        HasMeanZeroBilinearBound
          (cayleySquareComplex L R invA invB hL hR hLA hRB hTNC).rightCayleyGraph
          (2 * Real.sqrt (Delta : ℝ)) →
        let D := canonicalDataOfLocalCodeSample L R invA invB hL hR hLA hRB hTNC sample
        0 < D.blockLength ∧ 0 < D.encodedDimension ∧
          ∃ distance : Nat, D.HasParameters D.blockLength D.encodedDimension distance ∧
            (1 - 2 * rho) ^ 2 * D.blockLength ≤ (D.encodedDimension : ℝ) ∧
            delta * D.blockLength / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) ≤
              (distance : ℝ) ∧
            QEC.Coding.BoundedLocality
              (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile
              (Delta * Delta) := by sorry
