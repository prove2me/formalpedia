-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_globalPhaseEquivalent_conjugate
-- name    : QEC.Distillation.GeneratedUniversality.globalPhaseEquivalent_conjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:09:11.623249+00:00
-- url     : https://prove2.me/theorems/aa472208-cba7-453a-8d63-c9d2aa23eee3
-- title:
--   Generated Universality: global Phase Equivalent conjugate
-- statement:
--   Global-phase equivalence is compatible with conjugation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L100-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L100-L107

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

theorem QEC.Distillation.GeneratedUniversality.globalPhaseEquivalent_conjugate {n : Type u} [Fintype n] [DecidableEq n]
    {U V U' V' : UnitaryGate n}
    (hconjugator : GlobalPhaseEquivalent U V)
    (hconjugated : GlobalPhaseEquivalent U' V') :
    GlobalPhaseEquivalent (U * U' * U⁻¹) (V * V' * V⁻¹) := by sorry
