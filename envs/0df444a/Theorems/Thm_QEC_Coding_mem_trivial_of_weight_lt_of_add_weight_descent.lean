-- Prove2me | Theorems.Thm_QEC_Coding_mem_trivial_of_weight_lt_of_add_weight_descent
-- name    : QEC.Coding.mem_trivial_of_weight_lt_of_add_weight_descent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:27:59.88919+00:00
-- url     : https://prove2.me/theorems/3a75ffcd-12d8-4560-a039-17397d4852a9
-- title:
--   Coding: mem trivial of weight lt of add weight descent
-- statement:
--   Strict weight descent by trivial words makes every ambient word below the
--   threshold trivial. The induction preserves ambient membership and terminates
--   at the actual zero word, rather than assuming a distance conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/WeightDescent.lean#L25-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/WeightDescent.lean#L25-L52

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_CSS_WeightDescent
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F]
  [DecidableEq F] [Fintype ι]

theorem QEC.Coding.mem_trivial_of_weight_lt_of_add_weight_descent
    (ambient trivial : LinearCode F ι)
    (hsub : trivial.carrier ≤ ambient.carrier) (threshold : Nat)
    (hreduce : ∀ x : Word F ι, x ∈ ambient.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ y : Word F ι, y ∈ trivial.carrier ∧
        HammingWeight (x + y) < HammingWeight x)
    (x : Word F ι) (hx : x ∈ ambient.carrier)
    (hweight : HammingWeight x < threshold) : x ∈ trivial.carrier := by sorry
