-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimeScan_eq_none_of_forall
-- name    : QEC.Coding.TannerLiftedProduct.lpsPrimeScan_eq_none_of_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:47:18.724912+00:00
-- url     : https://prove2.me/theorems/baaad003-5dc1-409a-870b-6753144f4b44
-- title:
--   Tanner Lifted Product: lps Prime Scan eq none of forall
-- statement:
--   The Tanner Lifted Product construction uses the lps Prime Scan eq none of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L45-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L45-L52

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.lpsPrimeScan_eq_none_of_forall (p B n : ℕ)
    (h : ∀ q < n, ¬ lpsPrimeCandidate p B q) :
    lpsPrimeScan p B n = (none, n) := by sorry
