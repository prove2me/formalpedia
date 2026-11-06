-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_finiteSubsystem_subset
-- name    : QEC.Locality.exists_erasureRecovery_of_finiteSubsystem_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:55.870456+00:00
-- url     : https://prove2.me/theorems/1d8d250c-8ccc-478d-8fa9-bd1757dc5bc5
-- title:
--   Locality: exists erasure Recovery of finite Subsystem subset
-- statement:
--   Concrete qubit erasure recovery is monotone under shrinking the selected set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L524-L535
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L524-L535

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.exists_erasureRecovery_of_finiteSubsystem_subset
    (S T : FiniteSubsystem ι) (hST : S.selected ⊆ T.selected)
    (C : QuantumCode (Qubit.QubitRegister ι))
    (hRecovery : ∃ recovery : QuantumChannel T.complementSystem (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) T.complementSystem C
        T.erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) S.complementSystem C
        S.erasureChannelFromRegister recovery := by sorry
