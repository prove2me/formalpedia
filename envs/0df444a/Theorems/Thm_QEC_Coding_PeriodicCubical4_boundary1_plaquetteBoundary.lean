-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_boundary1_plaquetteBoundary
-- name    : QEC.Coding.PeriodicCubical4.boundary1_plaquetteBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:25:53.439714+00:00
-- url     : https://prove2.me/theorems/0514c8d1-72f8-4797-ba26-10ba596af1be
-- title:
--   Periodic Cubical4: boundary1 plaquette Boundary
-- statement:
--   The boundary of every plaquette has zero vertex boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Cellulation.lean#L388-L393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Cellulation.lean#L388-L393

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Cellulation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PeriodicCubical4
open scoped Classical
variable {L : Nat} [NeZero L]

theorem QEC.Coding.PeriodicCubical4.boundary1_plaquetteBoundary (p : Plaquette L) :
    boundary1 (plaquetteBoundary p) = 0 := by sorry
