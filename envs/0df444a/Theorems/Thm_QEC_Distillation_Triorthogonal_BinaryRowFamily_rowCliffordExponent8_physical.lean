-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCliffordExponent8_physical
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCliffordExponent8_physical
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:38:06.879205+00:00
-- url     : https://prove2.me/theorems/3e6fbf4d-fb36-43a2-8a25-31b034fe5356
-- title:
--   Binary Row Family: row Clifford Exponent8 physical
-- statement:
--   The complete BH12 Boolean residual exponent expressed on physical sites:
--   diagonal terms use `lambdaSingle`, and canonical unordered site pairs use `lambdaPair`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2259-L2294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2259-L2294

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCliffordExponent8_physical
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col) :
    R.rowCliffordExponent8 (R.rowCoefficientMap f) =
      2 * ((siteList Col).map fun p =>
        ((R.lambdaSingle p).val : ZMod 8) * bitLift8 (f p)).sum +
      4 * ((sitePairList Col).map fun pq =>
        ((R.lambdaPair pq.1 pq.2).val : ZMod 8) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum := by sorry
