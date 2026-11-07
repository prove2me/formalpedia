-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_append_right
-- name    : QEC.Coding.PauliErrorPath.stateAt_append_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:53:57.221466+00:00
-- url     : https://prove2.me/theorems/85d43e78-aa83-49b0-bc82-e691a4ba92fb
-- title:
--   Pauli Error Path: state At append right
-- statement:
--   After the join, concatenation left-transports the states of the right path by
--   the endpoint of the left path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L103-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L103-L114

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

theorem QEC.Coding.PauliErrorPath.stateAt_append_right (γ δ : PauliErrorPath (ι := ι)) (n : Nat)
    :
    (γ.append δ).stateAt (γ.increments.length + n) =
      binaryMul γ.endpoint (δ.stateAt n) := by sorry
