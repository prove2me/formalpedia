-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedToFullMeromorphic_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedToFullMeromorphic_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:28:06.614811+00:00
-- url     : https://prove2.me/theorems/7958cd61-e23f-4f96-95e1-d77c8efa9730
-- title:
--   Tanner Lifted Product: lps Original Generated To Full Meromorphic injective
-- statement:
--   The concrete generated-field map is faithful, without a generation assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicRestriction.lean#L374-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicRestriction.lean#L374-L379

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicGerms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedToFullMeromorphic_injective
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    Function.Injective (lpsOriginalGeneratedToFullMeromorphic N hpos hN) := by sorry
