-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_lambert_even_sub_four_add_odd_eq_not_four_dvd
-- name    : QEC.Coding.TannerLiftedProduct.tsum_lambert_even_sub_four_add_odd_eq_not_four_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:37:02.329465+00:00
-- url     : https://prove2.me/theorems/aabf4439-7a75-44e6-bd04-edceaf7ec8b6
-- title:
--   Tanner Lifted Product: tsum lambert even sub four add odd eq not four dvd
-- statement:
--   The Tanner Lifted Product construction uses the tsum lambert even sub four add odd eq not four dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L574-L581
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L574-L581

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.tsum_lambert_even_sub_four_add_odd_eq_not_four_dvd :
    (∑' n : ℕ,
        (jacobiLambertTerm (2 * (n + 1)) -
          jacobiLambertTerm (4 * (n + 1)) +
          jacobiLambertTerm (2 * n + 1))) =
      ∑' d : ℕ, if 4 ∣ d then 0 else jacobiLambertTerm d := by sorry
