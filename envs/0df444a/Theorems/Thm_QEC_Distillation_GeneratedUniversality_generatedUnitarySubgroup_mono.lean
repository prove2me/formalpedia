-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_generatedUnitarySubgroup_mono
-- name    : QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:44:13.923568+00:00
-- url     : https://prove2.me/theorems/a2f9fd03-bec3-4886-8eb7-d9d9bf1be196
-- title:
--   Generated Universality: generated Unitary Subgroup mono
-- statement:
--   Enlarging generators enlarges their generated subgroups.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L130-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L130-L134

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
set_option autoImplicit false
noncomputable section
universe u
open QEC
open QEC.Distillation
open QEC.Distillation.GeneratedUniversality
open Semantics
open scoped Matrix.Norms.Elementwise

theorem QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup_mono {n : Type u} [Fintype n] [DecidableEq n]
    {generators generators' : Set (UnitaryGate n)}
    (h : generators ⊆ generators') :
    generatedUnitarySubgroup generators ≤ generatedUnitarySubgroup generators' := by sorry
