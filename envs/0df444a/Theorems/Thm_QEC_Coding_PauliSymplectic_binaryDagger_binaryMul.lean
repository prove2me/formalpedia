-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryDagger_binaryMul
-- name    : QEC.Coding.PauliSymplectic.binaryDagger_binaryMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:27:50.039544+00:00
-- url     : https://prove2.me/theorems/5f15e806-0f78-4569-a0aa-15c49f871b32
-- title:
--   Pauli Symplectic: binary Dagger binary Mul
-- statement:
--   Dagger reverses binary Pauli multiplication.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L31-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L31-L44

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
open QEC.Coding.PauliSymplectic
omit [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.binaryDagger_binaryMul (P Q : Binary ι) :
    binaryDagger (binaryMul P Q) =
      binaryMul (binaryDagger Q) (binaryDagger P) := by sorry
