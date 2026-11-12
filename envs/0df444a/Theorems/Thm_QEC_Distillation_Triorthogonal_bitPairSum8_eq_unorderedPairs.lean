-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_bitPairSum8_eq_unorderedPairs
-- name    : QEC.Distillation.Triorthogonal.bitPairSum8_eq_unorderedPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:34:56.050292+00:00
-- url     : https://prove2.me/theorems/eacd0a79-b01e-4d84-85d7-db2b91b0f165
-- title:
--   Triorthogonal: bit Pair Sum8 eq unordered Pairs
-- statement:
--   The Triorthogonal construction uses the bit Pair Sum8 eq unordered Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L605-L613
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L605-L613

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

theorem QEC.Distillation.Triorthogonal.bitPairSum8_eq_unorderedPairs (xs : List (ZMod 2)) :
    bitPairSum8 xs =
      ((unorderedPairs xs).map fun pq => bitLift8 pq.1 * bitLift8 pq.2).sum := by sorry
