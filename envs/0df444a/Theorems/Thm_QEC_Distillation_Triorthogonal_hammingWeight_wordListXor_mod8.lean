-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_hammingWeight_wordListXor_mod8
-- name    : QEC.Distillation.Triorthogonal.hammingWeight_wordListXor_mod8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:33:49.062062+00:00
-- url     : https://prove2.me/theorems/64fb185c-5512-49aa-b1ee-fef52ea901e1
-- title:
--   Triorthogonal: hamming Weight word List Xor mod8
-- statement:
--   Exact finite-list inclusion-exclusion formula for binary Hamming weight modulo eight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L253-L273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L253-L273

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

theorem QEC.Distillation.Triorthogonal.hammingWeight_wordListXor_mod8
    (xs : List (Word (ZMod 2) Index)) :
    (HammingWeight (wordListXor xs) : ZMod 8) =
      wordWeightSum8 xs - 2 * wordPairSum8 xs + 4 * wordTripleSum8 xs := by sorry
