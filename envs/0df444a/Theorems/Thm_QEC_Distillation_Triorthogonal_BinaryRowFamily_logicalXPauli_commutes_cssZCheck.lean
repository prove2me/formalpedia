-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalXPauli_commutes_cssZCheck
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalXPauli_commutes_cssZCheck
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:05:31.58051+00:00
-- url     : https://prove2.me/theorems/25fac8f2-8cb7-4e5b-9694-3a91c7ece2d9
-- title:
--   Binary Row Family: logical XPauli commutes css ZCheck
-- statement:
--   Logical `X_a` commutes with every `Z`-type stabilizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L941-L947
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L941-L947

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalXPauli_commutes_cssZCheck
    (R : BinaryRowFamily OddRow EvenRow Col) (a : OddRow)
    {z : Word (ZMod 2) Col} (hz : z ∈ R.rowCode.dual.carrier) :
    PauliSymplectic.Commutes (R.logicalXPauli a)
      (PauliSymplectic.cssZCheck z) := by sorry
