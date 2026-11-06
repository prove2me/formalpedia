-- Prove2me | Theorems.Thm_QEC_Locality_support_embeddedLocalPauli_subset
-- name    : QEC.Locality.support_embeddedLocalPauli_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:20.522317+00:00
-- url     : https://prove2.me/theorems/0cf89d2c-fc4a-4039-9a4c-f0d73070a7ce
-- title:
--   Locality: support embedded Local Pauli subset
-- statement:
--   Every embedded local-Pauli branch is supported in the selected subsystem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean#L315-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean#L315-L323

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

theorem QEC.Locality.support_embeddedLocalPauli_subset (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    support (embeddedLocalPauli S p) ⊆ S.selected := by sorry
