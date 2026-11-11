-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_span_evenBasis_eq_evenCode
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.span_evenBasis_eq_evenCode
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:31:44.196104+00:00
-- url     : https://prove2.me/theorems/367ec9d5-9edc-4580-935f-c68ca167a6cd
-- title:
--   Binary Row Family: span even Basis eq even Code
-- statement:
--   The Binary Row Family construction uses the span even Basis eq even Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L913-L929
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L913-L929

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.span_evenBasis_eq_evenCode
    (R : BinaryRowFamily OddRow EvenRow Col) :
    Submodule.span (ZMod 2)
        (Set.range fun b : R.EvenBasisIndex =>
          (R.evenBasis b : Word (ZMod 2) Col)) =
      R.evenCode.carrier := by sorry
