-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_evenCode_eq_rowCode_inf_dual
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.evenCode_eq_rowCode_inf_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:01:35.182783+00:00
-- url     : https://prove2.me/theorems/288207cf-8926-4dfb-b262-e594979a911c
-- title:
--   Binary Row Family: even Code eq row Code inf dual
-- statement:
--   BH12 Lemma 1(iii): `G₀ = G ∩ G⊥`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L461-L485
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L461-L485

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.evenCode_eq_rowCode_inf_dual
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.evenCode.carrier = R.rowCode.carrier ⊓ R.rowCode.dual.carrier := by sorry
