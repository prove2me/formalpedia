-- Prove2me | Theorems.Thm_QEC_Locality_semanticStabilizerDistance_erasureRecoverableFromRegister
-- name    : QEC.Locality.semanticStabilizerDistance_erasureRecoverableFromRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:58:58.352778+00:00
-- url     : https://prove2.me/theorems/4f019f8a-76e5-4e5f-ad71-e65deceb0abd
-- title:
--   Locality: semantic Stabilizer Distance erasure Recoverable From Register
-- statement:
--   Every finite qubit subsystem smaller than a finite semantic stabilizer distance
--   has a typed CPTP recovery for its concrete erasure channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean#L379-L420
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean#L379-L420

import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
open QEC Semantics Coding
open scoped TensorProduct
open PauliSymplectic
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.semanticStabilizerDistance_erasureRecoverableFromRegister
    (Q : StabilizerCode.SourceValidBinary ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q d)
    (S : FiniteSubsystem ι) (hSelected : S.selected.card < d) :
    ∃ recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) S.complementSystem Q.1.code
        S.erasureChannelFromRegister recovery := by sorry
