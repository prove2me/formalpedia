-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_append_left
-- name    : QEC.Coding.PauliErrorPath.stateAt_append_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:28:16.072248+00:00
-- url     : https://prove2.me/theorems/91ae58bc-faf6-40ab-a807-9d963aa95017
-- title:
--   Pauli Error Path: state At append left
-- statement:
--   Before the join, concatenation has exactly the states of the left path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L94-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L94-L97

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

theorem QEC.Coding.PauliErrorPath.stateAt_append_left (γ δ : PauliErrorPath (ι := ι)) (n : Nat)
    (hn : n ≤ γ.increments.length) :
    (γ.append δ).stateAt n = γ.stateAt n := by sorry
