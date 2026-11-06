-- Prove2me | Theorems.Thm_QEC_Locality_weight_relative_embeddedLocalPauli_le_selected_card
-- name    : QEC.Locality.weight_relative_embeddedLocalPauli_le_selected_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:03.646462+00:00
-- url     : https://prove2.me/theorems/90ef97ec-7511-438e-89df-7ba2d967a955
-- title:
--   Locality: weight relative embedded Local Pauli le selected card
-- statement:
--   The relative Pauli of any two local twirl branches has weight at most `|U|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean#L337-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/SemanticDistanceErasure.lean#L337-L341

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

theorem QEC.Locality.weight_relative_embeddedLocalPauli_le_selected_card (S : FiniteSubsystem ι)
    (p q : LocalPauliWordIndex S) :
    weight (binaryMul (binaryDagger (embeddedLocalPauli S p))
      (embeddedLocalPauli S q)) ≤ S.selected.card := by sorry
