-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJPolynomial_exists_nonzero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJPolynomial_exists_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:32:19.663775+00:00
-- url     : https://prove2.me/theorems/a7645658-aa94-4b22-a12c-5c644254d28c
-- title:
--   Tanner Lifted Product: lps Original JPolynomial exists nonzero
-- statement:
--   Faithful original j evaluation makes every nonzero polynomial nonzero somewhere upstairs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicModularRatio.lean#L336-L347
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicModularRatio.lean#L336-L347

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJPolynomial_exists_nonzero
    (P : Polynomial ℂ) (hP : P ≠ 0) :
    ∃ τ : ℍ, P.eval (lpsOriginalJInvariant τ) ≠ 0 := by sorry
