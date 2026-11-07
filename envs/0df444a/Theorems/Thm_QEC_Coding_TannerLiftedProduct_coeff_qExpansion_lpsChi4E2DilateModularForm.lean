-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsChi4E2DilateModularForm
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsChi4E2DilateModularForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:15:01.384821+00:00
-- url     : https://prove2.me/theorems/4c0c21a9-5526-44c1-8c58-d05457877886
-- title:
--   Tanner Lifted Product: coeff q Expansion lps Chi4 E2 Dilate Modular Form
-- statement:
--   The Tanner Lifted Product construction uses the coeff q Expansion lps Chi4 E2 Dilate Modular Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L212-L217
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L212-L217

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsChi4E2DilateModularForm (m : ℕ) (hm : 0 < m) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsChi4E2DilateModularForm m hm))=
      if m∣n then -24*(ArithmeticFunction.sigma 1 (n/m):ℂ)*lpsChi4E2Character ((n/m:ℕ):ZMod 4) else 0 := by sorry
