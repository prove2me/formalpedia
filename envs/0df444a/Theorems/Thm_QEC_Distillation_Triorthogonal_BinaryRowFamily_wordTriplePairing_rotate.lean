-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_rotate
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_rotate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:32:42.369905+00:00
-- url     : https://prove2.me/theorems/3eb40a8e-cd55-4f36-93ad-2abdfd1c07dd
-- title:
--   Binary Row Family: word Triple Pairing rotate
-- statement:
--   The Binary Row Family construction uses the word Triple Pairing rotate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1072-L1077
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1072-L1077

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_rotate (x y z : Word (ZMod 2) Col) :
    wordTriplePairing x y z = wordTriplePairing z x y := by sorry
