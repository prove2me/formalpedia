-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_phaseAmplitude_pi_div_four_eq_of_natCast_eq
-- name    : QEC.Distillation.Triorthogonal.phaseAmplitude_pi_div_four_eq_of_natCast_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:33:46.110192+00:00
-- url     : https://prove2.me/theorems/fd48633e-22fc-41e1-a632-6f72e2a3946a
-- title:
--   Triorthogonal: phase Amplitude pi div four eq of nat Cast eq
-- statement:
--   Transport a proved modulo-eight exponent identity to the corresponding complex phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L309-L315
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L309-L315

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

theorem QEC.Distillation.Triorthogonal.phaseAmplitude_pi_div_four_eq_of_natCast_eq
    (n : Nat) (e : ZMod 8) (h : (n : ZMod 8) = e) :
    OneQubitMagic.phaseAmplitude (Real.pi / 4 * (n : Real)) =
      OneQubitMagic.phaseAmplitude (Real.pi / 4 * (e.val : Real)) := by sorry
