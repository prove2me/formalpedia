-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalChartToOverlap_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalChartToOverlap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:38:41.260208+00:00
-- url     : https://prove2.me/theorems/9334d520-109e-4c46-9080-2e1e1e558461
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Chart To Overlap injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Chart To Overlap injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L325-L336
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L325-L336

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalChartToOverlap_injective
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    Function.Injective (lpsOriginalIntegerNormalChartToOverlap N hN) := by sorry
