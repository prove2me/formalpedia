-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionFamilyIndex_decode_original
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyIndex_decode_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:12:52.299197+00:00
-- url     : https://prove2.me/theorems/47cad23e-f4db-400b-a0cf-86fd50b2f5da
-- title:
--   Tanner Lifted Product: lps Effective Quaternion Family Index decode original
-- statement:
--   Computed indices decode directly into the original cofinal semantic family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L164-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L164-L170

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyIndex_decode_original {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) (t : LPSGeneratorIndex p) :
    (lpsPSLEnumerationEquiv (lpsResiduePrimeSequence hp hp4 n).q)
        (lpsEffectiveQuaternionFamilyIndex hp hp4 n t) =
      lpsQuaternionFamilyLabel hp hp4 n t := by sorry
