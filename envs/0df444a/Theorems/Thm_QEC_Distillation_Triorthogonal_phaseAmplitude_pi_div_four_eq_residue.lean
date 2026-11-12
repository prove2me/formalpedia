-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_phaseAmplitude_pi_div_four_eq_residue
-- name    : QEC.Distillation.Triorthogonal.phaseAmplitude_pi_div_four_eq_residue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:50:16.049262+00:00
-- url     : https://prove2.me/theorems/0afeb89d-0356-4461-9282-c5c489596e4b
-- title:
--   Triorthogonal: phase Amplitude pi div four eq residue
-- statement:
--   Replace a natural exponent by its canonical `ℤ/8ℤ` representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L302-L306
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L302-L306

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

theorem QEC.Distillation.Triorthogonal.phaseAmplitude_pi_div_four_eq_residue (n : Nat) :
    OneQubitMagic.phaseAmplitude (Real.pi / 4 * (n : Real)) =
      OneQubitMagic.phaseAmplitude (Real.pi / 4 * ((n : ZMod 8).val : Real)) := by sorry
