-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_globalPhaseEquivalent_symm
-- name    : QEC.Distillation.GeneratedUniversality.globalPhaseEquivalent_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:43:40.495628+00:00
-- url     : https://prove2.me/theorems/a87f8e17-e03b-4ef1-aa3a-c30db61c4c9c
-- title:
--   Generated Universality: global Phase Equivalent symm
-- statement:
--   Global-phase equivalence is symmetric.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L48-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L48-L58

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

theorem QEC.Distillation.GeneratedUniversality.globalPhaseEquivalent_symm {n : Type u} [Fintype n] [DecidableEq n]
    {U V : UnitaryGate n} (h : GlobalPhaseEquivalent U V) :
    GlobalPhaseEquivalent V U := by sorry
