-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_hammingWeight_smul_cast8
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.hammingWeight_smul_cast8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:37:25.730957+00:00
-- url     : https://prove2.me/theorems/6880fc3e-26b1-4e0f-85e4-05f5f084cc2a
-- title:
--   Binary Row Family: hamming Weight smul cast8
-- statement:
--   The Binary Row Family construction uses the hamming Weight smul cast8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1471-L1477
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1471-L1477

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.hammingWeight_smul_cast8 (c : ZMod 2) (x : Word (ZMod 2) Col) :
    (HammingWeight (c • x) : ZMod 8) =
      bitLift8 c * (HammingWeight x : ZMod 8) := by sorry
