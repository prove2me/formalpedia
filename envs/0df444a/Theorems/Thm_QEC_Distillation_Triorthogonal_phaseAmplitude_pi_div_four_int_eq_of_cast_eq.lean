-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_phaseAmplitude_pi_div_four_int_eq_of_cast_eq
-- name    : QEC.Distillation.Triorthogonal.phaseAmplitude_pi_div_four_int_eq_of_cast_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:31:29.04601+00:00
-- url     : https://prove2.me/theorems/b31d56e7-1654-4314-8dbc-eeb8e4451169
-- title:
--   Triorthogonal: phase Amplitude pi div four int eq of cast eq
-- statement:
--   A `T`-phase exponent depends only on its residue modulo eight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L276-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L276-L291

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]

theorem QEC.Distillation.Triorthogonal.phaseAmplitude_pi_div_four_int_eq_of_cast_eq
    (m n : Int) (h : (m : ZMod 8) = (n : ZMod 8)) :
    OneQubitMagic.phaseAmplitude (Real.pi / 4 * (m : Real)) =
      OneQubitMagic.phaseAmplitude (Real.pi / 4 * (n : Real)) := by sorry
