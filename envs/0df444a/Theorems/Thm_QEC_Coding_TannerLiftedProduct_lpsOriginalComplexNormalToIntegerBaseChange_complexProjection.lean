-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalToIntegerBaseChange_complexProjection
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalToIntegerBaseChange_complexProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:53:08.034634+00:00
-- url     : https://prove2.me/theorems/065ba9af-e2bd-4d93-beed-0108c86b1678
-- title:
--   Tanner Lifted Product: lps Original Complex Normal To Integer Base Change complex Projection
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal To Integer Base Change complex Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalComplexNormalCharts.lean#L685-L689
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalComplexNormalCharts.lean#L685-L689

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalToIntegerBaseChange_complexProjection
    (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalComplexNormalToIntegerBaseChange N hN ≫ pullback.fst _ _ =
      lpsOriginalComplexNormalGluedToSpecC N hN := by sorry
