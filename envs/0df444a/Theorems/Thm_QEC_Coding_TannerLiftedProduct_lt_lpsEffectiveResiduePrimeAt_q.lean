-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lt_lpsEffectiveResiduePrimeAt_q
-- name    : QEC.Coding.TannerLiftedProduct.lt_lpsEffectiveResiduePrimeAt_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:47:18.931919+00:00
-- url     : https://prove2.me/theorems/402df911-cf05-4cc0-8577-e544522a254a
-- title:
--   Tanner Lifted Product: lt lps Effective Residue Prime At q
-- statement:
--   The Tanner Lifted Product construction uses the lt lps Effective Residue Prime At q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L25-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L25-L28

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.lt_lpsEffectiveResiduePrimeAt_q {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    B < (lpsEffectiveResiduePrimeAt hp hp4 B).q := by sorry
