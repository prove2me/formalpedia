-- Prove2me | Theorems.Thm_QEC_Locality_binarySupport_embedSelectedWord_subset
-- name    : QEC.Locality.binarySupport_embedSelectedWord_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:29:35.47239+00:00
-- url     : https://prove2.me/theorems/44cc5dc4-1569-40f7-9cd5-83dec3c85631
-- title:
--   Locality: binary Support embed Selected Word subset
-- statement:
--   The support of an embedded selected-coordinate word is contained in the selection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean#L49-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean#L49-L56

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

theorem QEC.Locality.binarySupport_embedSelectedWord_subset (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) :
    binarySupport (embedSelectedWord S w) ⊆ S.selected := by sorry
