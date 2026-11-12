-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_reducedRow_triple_even
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.reducedRow_triple_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:36:32.54022+00:00
-- url     : https://prove2.me/theorems/634f0de6-685e-4499-ae0b-245b89969838
-- title:
--   Binary Row Family: reduced Row triple even
-- statement:
--   The Binary Row Family construction uses the reduced Row triple even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1219-L1225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1219-L1225

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.reducedRow_triple_even
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {r s t : Sum OddRow R.EvenBasisIndex}
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    Even (tripleOverlap (R.reducedRow r) (R.reducedRow s) (R.reducedRow t)) := by sorry
