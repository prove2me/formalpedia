-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_substNegX_X_mul_jacobiPlusLogDerivative_odd
-- name    : QEC.Coding.TannerLiftedProduct.substNegX_X_mul_jacobiPlusLogDerivative_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:36:43.059129+00:00
-- url     : https://prove2.me/theorems/ea9533cf-7041-48aa-a152-3c4d655b6d6d
-- title:
--   Tanner Lifted Product: subst Neg X X mul jacobi Plus Log Derivative odd
-- statement:
--   The Tanner Lifted Product construction uses the subst Neg X X mul jacobi Plus Log Derivative odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L221-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L221-L231

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.substNegX_X_mul_jacobiPlusLogDerivative_odd (n : ℕ) :
    substNegX
        (PowerSeries.X * jacobiPlusLogDerivative (2 * n + 1)) =
      -jacobiLambertTerm (2 * n + 1) := by sorry
