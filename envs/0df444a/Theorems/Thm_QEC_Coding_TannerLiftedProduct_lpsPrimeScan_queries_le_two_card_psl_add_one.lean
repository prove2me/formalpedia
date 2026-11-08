-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimeScan_queries_le_two_card_psl_add_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsPrimeScan_queries_le_two_card_psl_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:17:40.2252+00:00
-- url     : https://prove2.me/theorems/80b18079-b906-427f-add7-ee7f9f4adb85
-- title:
--   Tanner Lifted Product: lps Prime Scan queries le two card psl add one
-- statement:
--   The candidate count is linear in the actual PSL output carrier size.
--   Arithmetic bit costs and sparse-matrix emission still need separate proofs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L84-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L84-L92

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsPrimeScan_queries_le_two_card_psl_add_one {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    (lpsPrimeScan p B ((lpsEffectiveResiduePrimeAt hp hp4 B).q + 1)).2 ≤
      2 * Fintype.card PSL(2, ZMod (lpsEffectiveResiduePrimeAt hp hp4 B).q) + 1 := by sorry
