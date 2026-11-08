-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGluedChartMap_cover
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGluedChartMap_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:52:33.343655+00:00
-- url     : https://prove2.me/theorems/cda48cdf-e82f-49cf-8c92-db56cdfa3296
-- title:
--   Tanner Lifted Product: lps Original Complex Normal Glued Chart Map cover
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal Glued Chart Map cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalComplexNormalCharts.lean#L473-L477
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalComplexNormalCharts.lean#L473-L477

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGluedChartMap_cover
    (N : ℕ) (hN : 0<N) (x : lpsOriginalComplexNormalGluedScheme N hN) :
    ∃ (b : Bool) (y : lpsOriginalComplexNormalSchemeChart N hN b),
      lpsOriginalComplexNormalGluedChartMap N hN b y=x := by sorry
