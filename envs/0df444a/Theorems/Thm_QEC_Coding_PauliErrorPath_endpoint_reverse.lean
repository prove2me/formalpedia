-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_reverse
-- name    : QEC.Coding.PauliErrorPath.endpoint_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:27:23.694448+00:00
-- url     : https://prove2.me/theorems/a561c199-10c7-4da0-bce6-5767c089b0e3
-- title:
--   Pauli Error Path: endpoint reverse
-- statement:
--   Reversal reaches the dagger of the original endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L83-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L83-L85

import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.PauliErrorPath

theorem QEC.Coding.PauliErrorPath.endpoint_reverse (γ : PauliErrorPath (ι := ι)) :
    γ.reverse.endpoint = binaryDagger γ.endpoint := by sorry
