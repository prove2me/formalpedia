-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_finitePrecisionUniversal_of_dense
-- name    : QEC.Distillation.GeneratedUniversality.finitePrecisionUniversal_of_dense
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:43:26.543866+00:00
-- url     : https://prove2.me/theorems/31ab1a0e-bb68-432f-abc0-34a6a27b6588
-- title:
--   Generated Universality: finite Precision Universal of dense
-- statement:
--   Dense generation entails finite-precision universality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L259-L266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L259-L266

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

theorem QEC.Distillation.GeneratedUniversality.finitePrecisionUniversal_of_dense {n : Type u} [Fintype n] [DecidableEq n]
    {generators : Set (UnitaryGate n)}
    (hdense : GeneratedUnitaryDense generators) :
    FinitePrecisionUniversal generators := by sorry
