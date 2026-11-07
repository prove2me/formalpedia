-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_accumulate_reverse_map_binaryDagger
-- name    : QEC.Coding.PauliErrorPath.accumulate_reverse_map_binaryDagger
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:28:13.552316+00:00
-- url     : https://prove2.me/theorems/d147d858-e54c-42c6-b26a-a8bc1b8021fc
-- title:
--   Pauli Error Path: accumulate reverse map binary Dagger
-- statement:
--   Accumulating reverse daggered increments gives the daggered product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L62-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L62-L74

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
omit [DecidableEq ι]

theorem QEC.Coding.PauliErrorPath.accumulate_reverse_map_binaryDagger (steps : List (Binary ι)) :
    accumulate (steps.reverse.map binaryDagger) =
      binaryDagger (accumulate steps) := by sorry
