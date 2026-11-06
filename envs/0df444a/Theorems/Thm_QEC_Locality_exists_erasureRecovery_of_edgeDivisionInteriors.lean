-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_edgeDivisionInteriors
-- name    : QEC.Locality.exists_erasureRecovery_of_edgeDivisionInteriors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:25:47.63419+00:00
-- url     : https://prove2.me/theorems/e35a71ac-c6ea-4100-a1c5-42df55f800bd
-- title:
--   Locality: exists erasure Recovery of edge Division Interiors
-- statement:
--   If every interior meets the exact #382 size and boundary hypotheses, the HKRS
--   interior adapter constructs a concrete recovery for their finite union using
--   the #373 pairwise-decoupled union theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L333-L368
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L333-L368

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.exists_erasureRecovery_of_edgeDivisionInteriors
    {κ : Type v} [Fintype κ] {m : Type w} [DecidableEq m]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hd : 0 < d) (hdn : d ≤ Fintype.card ι)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (beta exponent : ℝ)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hexponent : exponent < 1)
    (regions : m → Finset (ι × ι)) (active : Finset m)
    (hDivision : IsEdgeDivision P.fixedGeneratorInteractionGraph regions active)
    (hSmall : ∀ i, i ∈ active →
      ((edgeDivisionInterior regions active i).card : ℝ) ≤
        Real.rpow (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹)
    (hBoundary : ∀ i, i ∈ active →
      4 * (fixedGeneratorOuterBoundaryFinset P
        (edgeDivisionInterior regions active i)).card ≤ d) :
    ∃ recovery : QuantumChannel
        (familyUnionSubsystem
          (fun i => finiteSubsystemOfFinset (edgeDivisionInterior regions active i))
          active).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (familyUnionSubsystem
          (fun i => finiteSubsystemOfFinset (edgeDivisionInterior regions active i))
          active).complementSystem
        P.semanticCode
        (familyUnionSubsystem
          (fun i => finiteSubsystemOfFinset (edgeDivisionInterior regions active i))
          active).erasureChannelFromRegister recovery := by sorry
