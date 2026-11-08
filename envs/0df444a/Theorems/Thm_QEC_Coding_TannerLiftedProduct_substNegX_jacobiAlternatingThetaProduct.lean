-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_substNegX_jacobiAlternatingThetaProduct
-- name    : QEC.Coding.TannerLiftedProduct.substNegX_jacobiAlternatingThetaProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:36:56.594361+00:00
-- url     : https://prove2.me/theorems/c180caf8-d62d-41a1-a9b9-b88e3940aa82
-- title:
--   Tanner Lifted Product: subst Neg X jacobi Alternating Theta Product
-- statement:
--   The Tanner Lifted Product construction uses the subst Neg X jacobi Alternating Theta Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L93-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L93-L104

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.substNegX_jacobiAlternatingThetaProduct :
    substNegX jacobiAlternatingThetaProduct = jacobiThetaProduct := by sorry
