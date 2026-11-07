-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2DilateModularForm_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2DilateModularForm_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T22:27:35.497561+00:00
-- url     : https://prove2.me/theorems/ec2a2d6a-9506-428f-8980-1e9b1c56c517
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Dilate Modular Form apply
-- statement:
--   The Tanner Lifted Product construction uses the lps Quadratic E2 Dilate Modular Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L226-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L226-L228

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2DilateModularForm_apply (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (m : ℕ) (hm : 0 < m) (z : ℍ) :
    lpsQuadraticE2DilateModularForm q hq2 m hm z=lpsQuadraticE2Dilate q m hm z := by sorry
