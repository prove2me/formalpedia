-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_globalPhaseEquivalent_mul
-- name    : QEC.Distillation.GeneratedUniversality.globalPhaseEquivalent_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:44:06.711+00:00
-- url     : https://prove2.me/theorems/eac470c9-aa5a-4362-b049-3d24f3a91356
-- title:
--   Generated Universality: global Phase Equivalent mul
-- statement:
--   Global-phase equivalence is compatible with multiplication.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L74-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L74-L86

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

theorem QEC.Distillation.GeneratedUniversality.globalPhaseEquivalent_mul {n : Type u} [Fintype n] [DecidableEq n]
    {U V U' V' : UnitaryGate n}
    (hleft : GlobalPhaseEquivalent U V)
    (hright : GlobalPhaseEquivalent U' V') :
    GlobalPhaseEquivalent (U * U') (V * V') := by sorry
