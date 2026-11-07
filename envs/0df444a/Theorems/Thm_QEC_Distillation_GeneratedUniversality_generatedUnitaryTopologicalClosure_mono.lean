-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_generatedUnitaryTopologicalClosure_mono
-- name    : QEC.Distillation.GeneratedUniversality.generatedUnitaryTopologicalClosure_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:43:28.148196+00:00
-- url     : https://prove2.me/theorems/6c2a870c-243c-422e-b1dd-a4e4f3a82d7e
-- title:
--   Generated Universality: generated Unitary Topological Closure mono
-- statement:
--   Enlarging generators enlarges their generated topological closures.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L137-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L137-L143

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

theorem QEC.Distillation.GeneratedUniversality.generatedUnitaryTopologicalClosure_mono {n : Type u} [Fintype n] [DecidableEq n]
    {generators generators' : Set (UnitaryGate n)}
    (h : generators ⊆ generators') :
    generatedUnitaryTopologicalClosure generators ⊆
      generatedUnitaryTopologicalClosure generators' := by sorry
