-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalXPauli_commutes_logicalZPauli_iff
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalXPauli_commutes_logicalZPauli_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:12:36.104638+00:00
-- url     : https://prove2.me/theorems/6eef6434-afca-4069-8a5c-8217ffae94bf
-- title:
--   Binary Row Family: logical XPauli commutes logical ZPauli iff
-- statement:
--   The chosen logical Pauli representatives commute exactly off the diagonal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L967-L974
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L967-L974

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalXPauli_commutes_logicalZPauli_iff
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (a b : OddRow) :
    PauliSymplectic.Commutes (R.logicalXPauli a) (R.logicalZPauli b) ↔ a ≠ b := by sorry
