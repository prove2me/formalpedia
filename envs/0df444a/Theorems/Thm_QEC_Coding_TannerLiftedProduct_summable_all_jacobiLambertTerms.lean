-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_all_jacobiLambertTerms
-- name    : QEC.Coding.TannerLiftedProduct.summable_all_jacobiLambertTerms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:56:20.841577+00:00
-- url     : https://prove2.me/theorems/e2708311-8e49-46f7-b642-8742cc1b3bd8
-- title:
--   Tanner Lifted Product: summable all jacobi Lambert Terms
-- statement:
--   The Tanner Lifted Product construction uses the summable all jacobi Lambert Terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L393-L404
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L393-L404

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.summable_all_jacobiLambertTerms : Summable jacobiLambertTerm := by sorry
