-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_siteBitCount_eq_hammingWeight
-- name    : QEC.Distillation.Triorthogonal.siteBitCount_eq_hammingWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:35:56.534349+00:00
-- url     : https://prove2.me/theorems/6439e751-d8c4-4f71-be66-4d333a17df8b
-- title:
--   Triorthogonal: site Bit Count eq hamming Weight
-- statement:
--   The Triorthogonal construction uses the site Bit Count eq hamming Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L714-L739
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L714-L739

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

theorem QEC.Distillation.Triorthogonal.siteBitCount_eq_hammingWeight (bits : Qubit.Bitstring Index) :
    siteBitCount bits = HammingWeight (bitstringWordEquiv Index bits) := by sorry
