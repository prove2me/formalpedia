-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_boundary1_comp_boundary2
-- name    : QEC.Coding.PeriodicCubical4.boundary1_comp_boundary2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:50:38.931203+00:00
-- url     : https://prove2.me/theorems/3bb7229f-fba6-43a9-bbbf-4ccf484e3af8
-- title:
--   Periodic Cubical4: boundary1 comp boundary2
-- statement:
--   Link boundary after plaquette boundary is the zero linear map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Cellulation.lean#L428-L431
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Cellulation.lean#L428-L431

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Cellulation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PeriodicCubical4
open scoped Classical
variable {L : Nat} [NeZero L]

theorem QEC.Coding.PeriodicCubical4.boundary1_comp_boundary2 :
    (boundary1 (L := L)).comp boundary2 = 0 := by sorry
