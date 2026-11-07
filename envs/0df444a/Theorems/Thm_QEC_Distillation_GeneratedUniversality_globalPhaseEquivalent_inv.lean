-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_globalPhaseEquivalent_inv
-- name    : QEC.Distillation.GeneratedUniversality.globalPhaseEquivalent_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:44:01.804948+00:00
-- url     : https://prove2.me/theorems/08d62620-1fd4-4fae-9cdf-2dd68d29d63f
-- title:
--   Generated Universality: global Phase Equivalent inv
-- statement:
--   Global-phase equivalence is compatible with inversion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L89-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L89-L97

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

theorem QEC.Distillation.GeneratedUniversality.globalPhaseEquivalent_inv {n : Type u} [Fintype n] [DecidableEq n]
    {U V : UnitaryGate n} (h : GlobalPhaseEquivalent U V) :
    GlobalPhaseEquivalent U⁻¹ V⁻¹ := by sorry
