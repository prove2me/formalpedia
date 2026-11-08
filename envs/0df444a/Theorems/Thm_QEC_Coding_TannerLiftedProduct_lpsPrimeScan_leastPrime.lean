-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimeScan_leastPrime
-- name    : QEC.Coding.TannerLiftedProduct.lpsPrimeScan_leastPrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:48:00.474464+00:00
-- url     : https://prove2.me/theorems/191a75fc-2b62-4fbf-9979-3f8fde6c2e2f
-- title:
--   Tanner Lifted Product: lps Prime Scan least Prime
-- statement:
--   The measured scan actually returns the computed prime, in precisely q+1
--   candidate queries; it does not assume an output or a query bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L56-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L56-L64

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.lpsPrimeScan_leastPrime {p : ℕ} (hp : p.Prime) (B : ℕ) :
    lpsPrimeScan p B (lpsLeastPrimeAbove hp B + 1) =
      (some (lpsLeastPrimeAbove hp B), lpsLeastPrimeAbove hp B + 1) := by sorry
