-- Prove2me | Theorems.Thm_QEC_Coding_logical_weight_ge_of_add_weight_descent
-- name    : QEC.Coding.logical_weight_ge_of_add_weight_descent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:20.425422+00:00
-- url     : https://prove2.me/theorems/8b15f722-b9f1-4481-b26b-2fc284633957
-- title:
--   Coding: logical weight ge of add weight descent
-- statement:
--   Consequently every nontrivial logical representative has weight at least
--   the threshold. No nonempty logical sector or attained minimum is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/WeightDescent.lean#L56-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/WeightDescent.lean#L56-L67

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_CSS_WeightDescent
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F]
  [DecidableEq F] [Fintype ι]

theorem QEC.Coding.logical_weight_ge_of_add_weight_descent
    (ambient trivial : LinearCode F ι)
    (hsub : trivial.carrier ≤ ambient.carrier) (threshold : Nat)
    (hreduce : ∀ x : Word F ι, x ∈ ambient.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ y : Word F ι, y ∈ trivial.carrier ∧
        HammingWeight (x + y) < HammingWeight x)
    (x : Word F ι) (hx : x ∈ ambient.carrier)
    (hlogical : x ∉ trivial.carrier) : threshold ≤ HammingWeight x := by sorry
