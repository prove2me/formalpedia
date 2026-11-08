-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordCount_eq_geomSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordCount_eq_geomSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:27:59.08284+00:00
-- url     : https://prove2.me/theorems/a5ba4046-5136-4030-9710-20206a6b285e
-- title:
--   Tanner Lifted Product: lps Alternating Reduced Word Count eq geom Sum
-- statement:
--   The alternating reduced spheres have the geometric-sum cardinality
--   `1 + p + ... + p^n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimePowerCount.lean#L69-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimePowerCount.lean#L69-L84

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordCount_eq_geomSum
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    lpsAlternatingReducedWordCount hp.pos n =
      ∑ i ∈ Finset.range (n + 1), p ^ i := by sorry
