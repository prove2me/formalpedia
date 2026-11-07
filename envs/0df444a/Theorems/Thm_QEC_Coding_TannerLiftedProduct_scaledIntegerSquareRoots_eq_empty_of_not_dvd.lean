-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_scaledIntegerSquareRoots_eq_empty_of_not_dvd
-- name    : QEC.Coding.TannerLiftedProduct.scaledIntegerSquareRoots_eq_empty_of_not_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:38:39.630531+00:00
-- url     : https://prove2.me/theorems/6d872ea7-74cc-4505-ac05-300cefee94f2
-- title:
--   Tanner Lifted Product: scaled Integer Square Roots eq empty of not dvd
-- statement:
--   The Tanner Lifted Product construction uses the scaled Integer Square Roots eq empty of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceTheta.lean#L84-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceTheta.lean#L84-L94

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.scaledIntegerSquareRoots_eq_empty_of_not_dvd
    {m n : ℕ} (hm : 0 < m) (hdiv : ¬ m ^ 2 ∣ n) :
    scaledIntegerSquareRoots m n = ∅ := by sorry
