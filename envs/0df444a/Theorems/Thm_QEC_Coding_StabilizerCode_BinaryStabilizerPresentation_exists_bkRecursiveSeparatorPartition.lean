-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_exists_bkRecursiveSeparatorPartition
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.exists_bkRecursiveSeparatorPartition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:14:11.760203+00:00
-- url     : https://prove2.me/theorems/b8713301-c55e-418a-b5c7-0f1675f01567
-- title:
--   Binary Stabilizer Presentation: exists bk Recursive Separator Partition
-- statement:
--   The source-faithful BK finite recursive separator theorem on the actual fixed
--   generator interaction graph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L591-L608
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L591-L608

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.exists_bkRecursiveSeparatorPartition
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hDistance : SemanticStabilizerDistance P.code d)
    (hd : 0 < d) (vertices : Finset ι) :
    ∃ partition : BKRecursivePartition P.fixedGeneratorInteractionGraph d vertices,
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
