-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_evenCode_distinct_oddRows
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_evenCode_distinct_oddRows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:36:16.762032+00:00
-- url     : https://prove2.me/theorems/7eb2dfe4-4833-4df9-a053-854e222cc548
-- title:
--   Binary Row Family: word Triple Pairing even Code distinct odd Rows
-- statement:
--   An even-span word has zero cubic pairing with two distinct odd rows.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1163-L1172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1163-L1172

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_evenCode_distinct_oddRows
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier)
    {a b : OddRow} (hab : a ≠ b) :
    wordTriplePairing x (R.oddRow a) (R.oddRow b) = 0 := by sorry
