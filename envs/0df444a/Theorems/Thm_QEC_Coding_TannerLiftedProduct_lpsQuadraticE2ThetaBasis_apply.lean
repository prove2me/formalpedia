-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2ThetaBasis_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2ThetaBasis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:28:19.314497+00:00
-- url     : https://prove2.me/theorems/c2e0a445-98de-4dc8-8a91-81c63ae59168
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Theta Basis apply
-- statement:
--   The Tanner Lifted Product construction uses the lps Quadratic E2 Theta Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L318-L320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L318-L320

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2ThetaBasis_apply (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (a : Fin 5) (z : ℍ) :
    lpsQuadraticE2ThetaBasis q hq2 a z=
      lpsQuadraticE2Dilate q (2^a.val) (pow_pos (by decide) _) z := by sorry
