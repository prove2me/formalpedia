-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_q_le_two_mul_card_psl
-- name    : QEC.Coding.TannerLiftedProduct.LPSResiduePrime.q_le_two_mul_card_psl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:46:12.033835+00:00
-- url     : https://prove2.me/theorems/9c3003ae-fa6a-4f6a-908e-e50ebaf4b5f5
-- title:
--   LPSResidue Prime: q le two mul card psl
-- statement:
--   A coarse cardinal bound from the proved exact PSL order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L69-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L69-L80

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.LPSResiduePrime.q_le_two_mul_card_psl {p : ℕ}
    (a : LPSResiduePrime p) :
    a.q ≤ 2 * Fintype.card PSL(2, ZMod a.q) := by sorry
