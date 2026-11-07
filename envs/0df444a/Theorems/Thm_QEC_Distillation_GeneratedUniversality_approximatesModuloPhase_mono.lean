-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_approximatesModuloPhase_mono
-- name    : QEC.Distillation.GeneratedUniversality.approximatesModuloPhase_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:44:23.600218+00:00
-- url     : https://prove2.me/theorems/e5891b8f-266f-4544-a06e-06cf455b4676
-- title:
--   Generated Universality: approximates Modulo Phase mono
-- statement:
--   Approximation modulo phase is monotone under enlarging the generating set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L213-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L213-L220

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

theorem QEC.Distillation.GeneratedUniversality.approximatesModuloPhase_mono {n : Type u} [Fintype n] [DecidableEq n]
    {generators generators' : Set (UnitaryGate n)} {target : UnitaryGate n} {precision : Real}
    (h : generators ⊆ generators')
    (happrox : ApproximatesModuloPhase generators target precision) :
    ApproximatesModuloPhase generators' target precision := by sorry
