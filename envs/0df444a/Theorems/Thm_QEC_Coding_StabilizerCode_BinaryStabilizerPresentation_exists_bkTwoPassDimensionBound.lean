-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_exists_bkTwoPassDimensionBound
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.exists_bkTwoPassDimensionBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:50:00.300396+00:00
-- url     : https://prove2.me/theorems/452071e7-a8a4-4d7c-b000-c918272e8f5b
-- title:
--   Binary Stabilizer Presentation: exists bk Two Pass Dimension Bound
-- statement:
--   The genuine finite two-pass BK bridge.
--
--   The witnesses expose the two recursively constructed partitions and the actual regions used by
--   the dimension theorem.  In particular, `B` is not a second projection of the first pass: its
--   partition is constructed with `first.remainder` as its vertex set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean#L36-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean#L36-L107

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_TwoPassDimension
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open QEC Semantics Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.exists_bkTwoPassDimensionBound
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hDistance : SemanticStabilizerDistance P.code d) (hd : 0 < d) :
    ∃ first : BKRecursivePartition P.fixedGeneratorInteractionGraph d Finset.univ,
      ∃ second : BKRecursivePartition P.fixedGeneratorInteractionGraph d first.remainder,
        let A := bkPartitionRegion first
        let B := bkPartitionRegion second
        let C : FiniteSubsystem ι := ⟨second.remainder⟩
        Disjoint A.selected B.selected ∧
          Disjoint A.selected C.selected ∧
          Disjoint B.selected C.selected ∧
          A.selected ∪ B.selected ∪ C.selected = Finset.univ ∧
          ∃ recoveryA : QuantumChannel A.complementSystem (Qubit.QubitRegister ι),
            Correctable (Qubit.QubitRegister ι) A.complementSystem P.semanticCode
                A.erasureChannelFromRegister recoveryA ∧
              ∃ recoveryB : QuantumChannel B.complementSystem (Qubit.QubitRegister ι),
                Correctable (Qubit.QubitRegister ι) B.complementSystem P.semanticCode
                    B.erasureChannelFromRegister recoveryB ∧
                  P.encodedQubits ≤ C.selected.card ∧
                  first.remainder.card ≤ bkSumPreservingRecurrence
                    P.fixedGeneratorInteractionGraph d (Fintype.card ι) ∧
                  C.selected.card ≤ bkSeparatorRecurrence
                    P.fixedGeneratorInteractionGraph d first.remainder ∧
                  C.selected.card ≤ bkSumPreservingRecurrenceTwice
                    P.fixedGeneratorInteractionGraph d (Fintype.card ι) := by sorry
