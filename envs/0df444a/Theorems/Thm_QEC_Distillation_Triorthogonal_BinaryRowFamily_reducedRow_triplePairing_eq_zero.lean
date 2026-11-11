-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_reducedRow_triplePairing_eq_zero
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.reducedRow_triplePairing_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:36:20.512449+00:00
-- url     : https://prove2.me/theorems/e29c2c57-1900-4cf1-ba63-e10b5eec6178
-- title:
--   Binary Row Family: reduced Row triple Pairing eq zero
-- statement:
--   Pairwise-distinct reduced rows retain the BH12 cubic parity relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1181-L1217
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1181-L1217

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.reducedRow_triplePairing_eq_zero
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {r s t : Sum OddRow R.EvenBasisIndex}
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    wordTriplePairing (R.reducedRow r) (R.reducedRow s) (R.reducedRow t) = 0 := by sorry
