-- Prove2me | Theorems.Thm_QEC_Locality_support_relative_embeddedLocalPauli_subset
-- name    : QEC.Locality.support_relative_embeddedLocalPauli_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:03:13.909393+00:00
-- url     : https://prove2.me/theorems/0388b8ab-f1c3-4d35-a6a5-6965f7865589
-- title:
--   Locality: support relative embedded Local Pauli subset
-- statement:
--   Relative local-Pauli twirl branches remain supported on the selected subsystem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean#L326-L334
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean#L326-L334

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

theorem QEC.Locality.support_relative_embeddedLocalPauli_subset (S : FiniteSubsystem ι)
    (p q : LocalPauliWordIndex S) :
    support (binaryMul (binaryDagger (embeddedLocalPauli S p))
      (embeddedLocalPauli S q)) ⊆ S.selected := by sorry
