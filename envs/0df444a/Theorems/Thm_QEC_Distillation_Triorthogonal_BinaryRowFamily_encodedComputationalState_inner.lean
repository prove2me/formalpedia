-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedComputationalState_inner
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedComputationalState_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:09:02.585018+00:00
-- url     : https://prove2.me/theorems/6604cce6-e8fc-4301-8da7-75f67fca122e
-- title:
--   Binary Row Family: encoded Computational State inner
-- statement:
--   Encoded computational states are an orthonormal basis of the CSS carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L1041-L1050
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L1041-L1050

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedComputationalState_inner
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (x y : Qubit.Bitstring OddRow) :
    inner Complex (R.encodedComputationalState hR x)
        (R.encodedComputationalState hR y) = if x = y then 1 else 0 := by sorry
