-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionFamilyIndex_decode
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyIndex_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:46:17.751681+00:00
-- url     : https://prove2.me/theorems/157b6a97-8dc9-4eab-bf59-2e647fe17563
-- title:
--   Tanner Lifted Product: lps Effective Quaternion Family Index decode
-- statement:
--   Computed vertex numbering decodes to the actual effective family label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L140-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L140-L145

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyIndex_decode {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) (t : LPSGeneratorIndex p) :
    (lpsPSLEnumerationEquiv (lpsEffectiveResiduePrimeAt hp hp4 n).q)
      (lpsEffectiveQuaternionFamilyIndex hp hp4 n t) =
        lpsEffectiveQuaternionFamilyLabel hp hp4 n t := by sorry
