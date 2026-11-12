-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_list_sum_mul_sum_split_pairs
-- name    : QEC.Distillation.Triorthogonal.list_sum_mul_sum_split_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:35:03.917121+00:00
-- url     : https://prove2.me/theorems/2c46dc53-d6ce-4905-bf31-c109bfe74798
-- title:
--   Triorthogonal: list sum mul sum split pairs
-- statement:
--   A product of two list sums split into diagonal and unordered cross terms.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L666-L672
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L666-L672

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

theorem QEC.Distillation.Triorthogonal.list_sum_mul_sum_split_pairs {A R : Type*} [CommRing R]
    (xs : List A) (f g : A → R) :
    (xs.map f).sum * (xs.map g).sum =
      (xs.map fun x => f x * g x).sum +
        ((unorderedPairs xs).map fun pq =>
          f pq.1 * g pq.2 + f pq.2 * g pq.1).sum := by sorry
