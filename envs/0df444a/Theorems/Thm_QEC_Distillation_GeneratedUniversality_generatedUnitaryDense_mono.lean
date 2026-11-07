-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_generatedUnitaryDense_mono
-- name    : QEC.Distillation.GeneratedUniversality.generatedUnitaryDense_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:09:12.227901+00:00
-- url     : https://prove2.me/theorems/e46225ed-f249-4069-8bc2-35ac8579f2bc
-- title:
--   Generated Universality: generated Unitary Dense mono
-- statement:
--   Generated density is monotone under enlarging the generating set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L146-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L146-L155

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

theorem QEC.Distillation.GeneratedUniversality.generatedUnitaryDense_mono {n : Type u} [Fintype n] [DecidableEq n]
    {generators generators' : Set (UnitaryGate n)}
    (h : generators ⊆ generators')
    (hdense : GeneratedUnitaryDense generators) :
    GeneratedUnitaryDense generators' := by sorry
