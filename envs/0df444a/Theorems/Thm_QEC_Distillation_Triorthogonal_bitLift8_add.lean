-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_bitLift8_add
-- name    : QEC.Distillation.Triorthogonal.bitLift8_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:32:55.020207+00:00
-- url     : https://prove2.me/theorems/22d7d7ce-ad36-41dc-8e6a-555d113d1106
-- title:
--   Triorthogonal: bit Lift8 add
-- statement:
--   Lifting binary XOR to `ℤ/8ℤ` produces the usual inclusion-exclusion step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L41-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L41-L43

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

theorem QEC.Distillation.Triorthogonal.bitLift8_add (x y : ZMod 2) :
    bitLift8 (x + y) = bitLift8 x + bitLift8 y - 2 * bitLift8 x * bitLift8 y := by sorry
