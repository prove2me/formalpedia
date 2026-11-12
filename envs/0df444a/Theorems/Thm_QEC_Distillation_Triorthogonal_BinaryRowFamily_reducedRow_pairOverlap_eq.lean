-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_reducedRow_pairOverlap_eq
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.reducedRow_pairOverlap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:37:21.837205+00:00
-- url     : https://prove2.me/theorems/8d46255e-198c-4106-a2ac-90d099be24f1
-- title:
--   Binary Row Family: reduced Row pair Overlap eq
-- statement:
--   The Binary Row Family construction uses the reduced Row pair Overlap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1463-L1469
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1463-L1469

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.reducedRow_pairOverlap_eq
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {r s : R.ReducedRowIndex} (hrs : r ≠ s) :
    pairOverlap (R.reducedRow r) (R.reducedRow s) = 2 * R.rowPairGamma r s := by sorry
