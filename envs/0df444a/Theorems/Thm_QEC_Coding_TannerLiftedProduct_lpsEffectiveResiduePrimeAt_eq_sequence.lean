-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveResiduePrimeAt_eq_sequence
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveResiduePrimeAt_eq_sequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:10:24.621409+00:00
-- url     : https://prove2.me/theorems/d1737487-4330-49f2-8c03-cda5535c1e0d
-- title:
--   Tanner Lifted Product: lps Effective Residue Prime At eq sequence
-- statement:
--   Both actual family carriers use exactly the same computed arithmetic certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L31-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L31-L33

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveResiduePrimeAt_eq_sequence {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    lpsEffectiveResiduePrimeAt hp hp4 n = lpsResiduePrimeSequence hp hp4 n := by sorry
