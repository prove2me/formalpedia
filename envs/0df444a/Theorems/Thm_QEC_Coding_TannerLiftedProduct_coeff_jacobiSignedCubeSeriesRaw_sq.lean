-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeriesRaw_sq
-- name    : QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeriesRaw_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:16:01.565812+00:00
-- url     : https://prove2.me/theorems/361cdf80-8f89-4ba1-a78f-712231c8b25b
-- title:
--   Tanner Lifted Product: coeff jacobi Signed Cube Series Raw sq
-- statement:
--   The Tanner Lifted Product construction uses the coeff jacobi Signed Cube Series Raw sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L369-L393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L369-L393

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeriesRaw_sq (n : ℕ) :
    PowerSeries.coeff n (jacobiSignedCubeSeriesRaw ^ 2) =
      ∑ p : JacobiCubePair n, jacobiCubePairWeight p.1 := by sorry
