-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_cssQuantumCode_finrank_carrier
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.cssQuantumCode_finrank_carrier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T13:51:52.133726+00:00
-- url     : https://prove2.me/theorems/ba503462-ccde-47fb-a28f-6ce4ce296757
-- title:
--   Binary Row Family: css Quantum Code finrank carrier
-- statement:
--   The semantic CSS carrier has dimension `2^k`, where `k` is the odd-row count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L614-L619
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L614-L619

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.cssQuantumCode_finrank_carrier
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Module.finrank Complex R.cssQuantumCode.carrier = 2 ^ Fintype.card OddRow := by sorry
