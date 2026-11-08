-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_lambert_not_four_dvd
-- name    : QEC.Coding.TannerLiftedProduct.tsum_lambert_not_four_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:36:54.36482+00:00
-- url     : https://prove2.me/theorems/b805c2f0-3992-425a-9037-7e9b2eabbd2e
-- title:
--   Tanner Lifted Product: tsum lambert not four dvd
-- statement:
--   The Tanner Lifted Product construction uses the tsum lambert not four dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L516-L572
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L516-L572

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
set_option maxHeartbeats 800000

theorem QEC.Coding.TannerLiftedProduct.tsum_lambert_not_four_dvd :
    (∑' d : ℕ, if 4 ∣ d then 0 else jacobiLambertTerm d) =
      (∑' d : ℕ, jacobiLambertTerm d) -
        ∑' n : ℕ, jacobiLambertTerm (4 * n) := by sorry
