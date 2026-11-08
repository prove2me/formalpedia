-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicCovectors_finiteDimensional
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicCovectors_finiteDimensional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:16:20.741965+00:00
-- url     : https://prove2.me/theorems/2fe49063-2aae-4002-ae6a-22765ea4760c
-- title:
--   Tanner Lifted Product: lps Original Holomorphic Covectors finite Dimensional
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Holomorphic Covectors finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGlobalDifferentialFiniteness.lean#L32-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGlobalDifferentialFiniteness.lean#L32-L37

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRegularDifferentialFiniteness
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalDifferentialFiniteness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry MatrixGroups UpperHalfPlane ModularForm Modular Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] originalNativeGlobalComplexModule
include hpos hN

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicCovectors_finiteDimensional :
    FiniteDimensional ℂ (LPSOriginalHolomorphicCovectorSections N hN) := by sorry
