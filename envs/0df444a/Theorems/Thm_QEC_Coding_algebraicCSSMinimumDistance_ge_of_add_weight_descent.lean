-- Prove2me | Theorems.Thm_QEC_Coding_algebraicCSSMinimumDistance_ge_of_add_weight_descent
-- name    : QEC.Coding.algebraicCSSMinimumDistance_ge_of_add_weight_descent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:44:18.059545+00:00
-- url     : https://prove2.me/theorems/3f65f38b-9cfa-400f-b203-36d466079b51
-- title:
--   Coding: algebraic CSSMinimum Distance ge of add weight descent
-- statement:
--   The same reduction in both actual CSS sectors bounds any attained CSS
--   minimum. This is only the final descent bridge: the two geometric reduction
--   premises must still be proved from expansion and local-code robustness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/WeightDescent.lean#L72-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/WeightDescent.lean#L72-L93

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_CSS_WeightDescent
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F]
  [DecidableEq F] [Fintype ι]

theorem QEC.Coding.algebraicCSSMinimumDistance_ge_of_add_weight_descent
    (xCode zCode : LinearCode F ι)
    (hX : xCode.carrier ≤ zCode.dual.carrier)
    (hZ : zCode.carrier ≤ xCode.dual.carrier) (threshold : Nat)
    (hreduceX : ∀ x : Word F ι, x ∈ zCode.dual.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ y : Word F ι, y ∈ xCode.carrier ∧
        HammingWeight (x + y) < HammingWeight x)
    (hreduceZ : ∀ x : Word F ι, x ∈ xCode.dual.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ y : Word F ι, y ∈ zCode.carrier ∧
        HammingWeight (x + y) < HammingWeight x)
    {distance : Nat}
    (hmin : AlgebraicCSSMinimumDistance xCode zCode distance) :
    threshold ≤ distance := by sorry
