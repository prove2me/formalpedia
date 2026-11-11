-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_hammingWeight_cast8
-- name    : QEC.Distillation.Triorthogonal.hammingWeight_cast8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:30:13.943423+00:00
-- url     : https://prove2.me/theorems/14475ab3-9958-40af-8816-d4965dca3a57
-- title:
--   Triorthogonal: hamming Weight cast8
-- statement:
--   Hamming weight is the sum of canonical binary lifts in `ℤ/8ℤ`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L81-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L81-L95

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

theorem QEC.Distillation.Triorthogonal.hammingWeight_cast8 (x : Word (ZMod 2) Index) :
    (HammingWeight x : ZMod 8) = ∑ p, bitLift8 (x p) := by sorry
