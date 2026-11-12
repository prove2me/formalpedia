-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_hammingWeight_even_of_mem_evenCode
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.hammingWeight_even_of_mem_evenCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:37:25.302666+00:00
-- url     : https://prove2.me/theorems/b9610fb8-2495-4053-bd4a-a422bcf0f77d
-- title:
--   Binary Row Family: hamming Weight even of mem even Code
-- statement:
--   The Binary Row Family construction uses the hamming Weight even of mem even Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1404-L1410
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1404-L1410

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.hammingWeight_even_of_mem_evenCode
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier) :
    Even (HammingWeight x) := by sorry
