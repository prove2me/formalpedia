-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_take
-- name    : QEC.Coding.PauliErrorPath.stateAt_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:27:27.735387+00:00
-- url     : https://prove2.me/theorems/eedbda36-c401-4db3-a955-3fa99051c550
-- title:
--   Pauli Error Path: state At take
-- statement:
--   A prefix state is unchanged when it is viewed inside a longer prefix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L88-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L88-L91

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

theorem QEC.Coding.PauliErrorPath.stateAt_take (γ : PauliErrorPath (ι := ι)) (n m : Nat)
    (hm : m ≤ n) :
    (γ.take n).stateAt m = γ.stateAt m := by sorry
