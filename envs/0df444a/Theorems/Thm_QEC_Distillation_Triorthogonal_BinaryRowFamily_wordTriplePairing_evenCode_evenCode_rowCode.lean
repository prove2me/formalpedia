-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_evenCode_evenCode_rowCode
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_evenCode_evenCode_rowCode
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:36:12.092197+00:00
-- url     : https://prove2.me/theorems/b90bb0d5-c41e-4dbc-90a9-ac32e8ad88fc
-- title:
--   Binary Row Family: word Triple Pairing even Code even Code row Code
-- statement:
--   Two even-span words have zero cubic pairing with the whole row span.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1147-L1160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1147-L1160

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
universe uO uE uC
open QEC.Distillation.Triorthogonal.BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_evenCode_evenCode_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x y z : Word (ZMod 2) Col}
    (hx : x ∈ R.evenCode.carrier) (hy : y ∈ R.evenCode.carrier)
    (hz : z ∈ R.rowCode.carrier) : wordTriplePairing x y z = 0 := by sorry
