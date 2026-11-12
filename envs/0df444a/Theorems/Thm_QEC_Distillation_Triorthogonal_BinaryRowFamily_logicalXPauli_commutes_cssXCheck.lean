-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalXPauli_commutes_cssXCheck
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalXPauli_commutes_cssXCheck
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:05:26.314451+00:00
-- url     : https://prove2.me/theorems/72e1e132-d33e-4745-a8b6-9349d8a6ece8
-- title:
--   Binary Row Family: logical XPauli commutes css XCheck
-- statement:
--   Logical `X_a` commutes with every `X`-type stabilizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L933-L938
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L933-L938

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalXPauli_commutes_cssXCheck
    (R : BinaryRowFamily OddRow EvenRow Col) (a : OddRow)
    (x : Word (ZMod 2) Col) :
    PauliSymplectic.Commutes (R.logicalXPauli a)
      (PauliSymplectic.cssXCheck x) := by sorry
