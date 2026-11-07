-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_reverse_increments
-- name    : QEC.Coding.PauliErrorPath.reverse_increments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:27:49.150309+00:00
-- url     : https://prove2.me/theorems/c44be1e7-c60c-4792-af9f-8ff4a5cfc2cf
-- title:
--   Pauli Error Path: reverse increments
-- statement:
--   The Pauli Error Path construction uses the reverse increments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L77-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L77-L79

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

theorem QEC.Coding.PauliErrorPath.reverse_increments (γ : PauliErrorPath (ι := ι)) :
    γ.reverse.increments = γ.increments.reverse.map binaryDagger := by sorry

attribute [defeq] QEC.Coding.PauliErrorPath.reverse_increments
