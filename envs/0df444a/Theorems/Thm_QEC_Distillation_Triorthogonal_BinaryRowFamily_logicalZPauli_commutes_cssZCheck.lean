-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalZPauli_commutes_cssZCheck
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalZPauli_commutes_cssZCheck
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:07:15.492439+00:00
-- url     : https://prove2.me/theorems/adb6403b-3780-4235-9c04-06f46dc35d1f
-- title:
--   Binary Row Family: logical ZPauli commutes css ZCheck
-- statement:
--   Logical `Z_a` commutes with every `Z`-type stabilizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L950-L955
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L950-L955

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Coding Semantics
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe uR uM uI
universe u v w
variable {OddRow : Type u} {EvenRow : Type v} {Col : Type w}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
open QEC.Distillation.Triorthogonal.BinaryRowFamily

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalZPauli_commutes_cssZCheck
    (R : BinaryRowFamily OddRow EvenRow Col) (a : OddRow)
    (z : Word (ZMod 2) Col) :
    PauliSymplectic.Commutes (R.logicalZPauli a)
      (PauliSymplectic.cssZCheck z) := by sorry
