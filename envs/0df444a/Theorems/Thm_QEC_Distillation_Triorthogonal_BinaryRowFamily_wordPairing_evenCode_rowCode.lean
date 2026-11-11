-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordPairing_evenCode_rowCode
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.wordPairing_evenCode_rowCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:12:10.910393+00:00
-- url     : https://prove2.me/theorems/6d34e286-5b4e-4803-a861-0ab102276353
-- title:
--   Binary Row Family: word Pairing even Code row Code
-- statement:
--   The even span is orthogonal to the entire row span.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L402-L410
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L402-L410

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.wordPairing_evenCode_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x y : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier)
    (hy : y ∈ R.rowCode.carrier) : wordPairing x y = 0 := by sorry
