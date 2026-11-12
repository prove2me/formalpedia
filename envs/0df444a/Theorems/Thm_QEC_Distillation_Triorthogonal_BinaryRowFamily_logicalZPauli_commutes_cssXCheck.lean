-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalZPauli_commutes_cssXCheck
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalZPauli_commutes_cssXCheck
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:07:27.484447+00:00
-- url     : https://prove2.me/theorems/0fb68e61-14f9-48ee-955d-7a005207a90d
-- title:
--   Binary Row Family: logical ZPauli commutes css XCheck
-- statement:
--   Logical `Z_a` commutes with every `X`-type stabilizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L958-L964
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L958-L964

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalZPauli_commutes_cssXCheck
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (a : OddRow) {x : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier) :
    PauliSymplectic.Commutes (R.logicalZPauli a)
      (PauliSymplectic.cssXCheck x) := by sorry
