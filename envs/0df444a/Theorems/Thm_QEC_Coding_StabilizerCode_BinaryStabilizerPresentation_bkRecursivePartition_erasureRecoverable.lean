-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_bkRecursivePartition_erasureRecoverable
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.bkRecursivePartition_erasureRecoverable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:33:59.106186+00:00
-- url     : https://prove2.me/theorems/1e732788-8bc2-4161-9d3f-3b99a42b668c
-- title:
--   Binary Stabilizer Presentation: bk Recursive Partition erasure Recoverable
-- statement:
--   The union of all small pieces in a BK recursive partition has a concrete CPTP
--   erasure recovery: distance handles each leaf, and source decoupling handles the
--   finite union.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L562-L585
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L562-L585

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open QEC Semantics Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.bkRecursivePartition_erasureRecoverable
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hDistance : SemanticStabilizerDistance P.code d)
    (vertices : Finset ι)
    (partition : BKRecursivePartition P.fixedGeneratorInteractionGraph d vertices) :
    ∃ recovery : QuantumChannel
        (familyUnionSubsystem (fun region : Finset ι => (⟨region⟩ : FiniteSubsystem ι))
          partition.pieces).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (familyUnionSubsystem (fun region : Finset ι => (⟨region⟩ : FiniteSubsystem ι))
          partition.pieces).complementSystem
        P.semanticCode
        (familyUnionSubsystem (fun region : Finset ι => (⟨region⟩ : FiniteSubsystem ι))
          partition.pieces).erasureChannelFromRegister recovery := by sorry
