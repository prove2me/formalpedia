-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_lambert_even_sub_four_add_odd
-- name    : QEC.Coding.TannerLiftedProduct.tsum_lambert_even_sub_four_add_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:36:54.019213+00:00
-- url     : https://prove2.me/theorems/7caef432-7e23-47bd-97c5-2aafc4576665
-- title:
--   Tanner Lifted Product: tsum lambert even sub four add odd
-- statement:
--   The Tanner Lifted Product construction uses the tsum lambert even sub four add odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L445-L464
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L445-L464

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.tsum_lambert_even_sub_four_add_odd :
    (∑' n : ℕ,
        (jacobiLambertTerm (2 * (n + 1)) -
          jacobiLambertTerm (4 * (n + 1)) +
          jacobiLambertTerm (2 * n + 1))) =
      (∑' d : ℕ, jacobiLambertTerm d) -
        ∑' n : ℕ, jacobiLambertTerm (4 * n) := by sorry
