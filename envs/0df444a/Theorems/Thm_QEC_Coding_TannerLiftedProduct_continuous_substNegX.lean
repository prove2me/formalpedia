-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_continuous_substNegX
-- name    : QEC.Coding.TannerLiftedProduct.continuous_substNegX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:35:48.404788+00:00
-- url     : https://prove2.me/theorems/8e1d879c-4589-4197-ae20-b73b343aa411
-- title:
--   Tanner Lifted Product: continuous subst Neg X
-- statement:
--   The Tanner Lifted Product construction uses the continuous subst Neg X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L67-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L67-L75

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.continuous_substNegX : Continuous substNegX := by sorry
