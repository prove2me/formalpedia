-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_boundary3_comp_boundary4
-- name    : QEC.Coding.PeriodicCubical4.boundary3_comp_boundary4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:49:59.443265+00:00
-- url     : https://prove2.me/theorems/29450900-53c9-42bd-8a8c-d91928900be8
-- title:
--   Periodic Cubical4: boundary3 comp boundary4
-- statement:
--   Cube boundary after four-cell boundary is the zero linear map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Cellulation.lean#L440-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Cellulation.lean#L440-L443

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Cellulation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PeriodicCubical4
open scoped Classical
variable {L : Nat} [NeZero L]

theorem QEC.Coding.PeriodicCubical4.boundary3_comp_boundary4 :
    (boundary3 (L := L)).comp boundary4 = 0 := by sorry
