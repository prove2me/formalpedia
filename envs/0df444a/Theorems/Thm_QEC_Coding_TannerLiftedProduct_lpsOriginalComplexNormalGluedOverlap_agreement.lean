-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGluedOverlap_agreement
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGluedOverlap_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:55:35.41454+00:00
-- url     : https://prove2.me/theorems/07551462-b545-4a10-9e07-fed0bfbdece0
-- title:
--   Tanner Lifted Product: lps Original Complex Normal Glued Overlap agreement
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal Glued Overlap agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalComplexNormalCharts.lean#L480-L511
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalComplexNormalCharts.lean#L480-L511

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLaurentNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open scoped TensorProduct
noncomputable section
local notation "JC" => FractionRing (Polynomial ℂ)
attribute [local instance] QEC.Coding.TannerLiftedProduct.complexGluingDictionary001
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGluedOverlap_agreement
    (N : ℕ) (hN : 0<N) :
    lpsOriginalComplexNormalSchemeOverlapMap N hN false ≫
      lpsOriginalComplexNormalGluedChartMap N hN false=
    lpsOriginalComplexNormalSchemeOverlapMap N hN true ≫
      lpsOriginalComplexNormalGluedChartMap N hN true := by sorry
