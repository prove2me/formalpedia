-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_swap_left
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_swap_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:32:42.986406+00:00
-- url     : https://prove2.me/theorems/74277f4f-4d2c-4d11-bbd6-bf135ab4e7cb
-- title:
--   Binary Row Family: word Triple Pairing swap left
-- statement:
--   The Binary Row Family construction uses the word Triple Pairing swap left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1065-L1070
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1065-L1070

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_swap_left (x y z : Word (ZMod 2) Col) :
    wordTriplePairing x y z = wordTriplePairing y x z := by sorry
