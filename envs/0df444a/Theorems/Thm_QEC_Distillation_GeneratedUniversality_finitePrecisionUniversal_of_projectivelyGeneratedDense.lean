-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_finitePrecisionUniversal_of_projectivelyGeneratedDense
-- name    : QEC.Distillation.GeneratedUniversality.finitePrecisionUniversal_of_projectivelyGeneratedDense
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:44:15.092231+00:00
-- url     : https://prove2.me/theorems/ad74b4c6-c7b5-448e-81a8-9408372d0dfa
-- title:
--   Generated Universality: finite Precision Universal of projectively Generated Dense
-- statement:
--   Projective generated density entails finite-precision universality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L269-L277
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L269-L277

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

theorem QEC.Distillation.GeneratedUniversality.finitePrecisionUniversal_of_projectivelyGeneratedDense
    {n : Type u} [Fintype n] [DecidableEq n]
    {generators : Set (UnitaryGate n)}
    (hdense : ProjectivelyGeneratedDense generators) :
    FinitePrecisionUniversal generators := by sorry
