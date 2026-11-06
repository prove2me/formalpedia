-- Prove2me | Theorems.Thm_QEC_Locality_embeddedLocalPauliKrausFamily_toQuantumChannel_eq_localPauliTwirl
-- name    : QEC.Locality.embeddedLocalPauliKrausFamily_toQuantumChannel_eq_localPauliTwirl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:02:56.319059+00:00
-- url     : https://prove2.me/theorems/07fc6bc7-a9d1-4d95-98c1-42492b0dbae5
-- title:
--   Locality: embedded Local Pauli Kraus Family to Quantum Channel eq local Pauli Twirl
-- statement:
--   The M3-ready embedded binary-Pauli channel is exactly the concrete local Pauli twirl.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean#L292-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean#L292-L312

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

theorem QEC.Locality.embeddedLocalPauliKrausFamily_toQuantumChannel_eq_localPauliTwirl
    (S : FiniteSubsystem ι) :
    (binaryPauliKrausFamily (embeddedLocalPauli S)
      (fun _ => localPauliAmplitude S)).toQuantumChannel
        (embeddedLocalPauliKrausFamily_complete S) =
      localPauliTwirl S := by sorry
