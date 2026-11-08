-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionFamilyLabel_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyLabel_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:46:12.464479+00:00
-- url     : https://prove2.me/theorems/71103be1-265a-4050-bf72-5a17431a258f
-- title:
--   Tanner Lifted Product: lps Effective Quaternion Family Label eq
-- statement:
--   Computation preserves the actual semantic label at the computed prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L119-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L119-L124

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyLabel_eq {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    lpsEffectiveQuaternionFamilyLabel hp hp4 n =
      lpsQuaternionLabel (lpsEffectiveResiduePrimeAt hp hp4 n) := by sorry
