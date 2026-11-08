-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalCharts_complexBaseChangePullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalCharts_complexBaseChangePullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:59:50.875239+00:00
-- url     : https://prove2.me/theorems/a817f179-7d73-4340-8bb6-d9dcae4af6b2
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Charts complex Base Change Pullback
-- statement:
--   The genuine integer normalization intersection remains a pullback under
--   extension to complex scalars. The morphisms are the actual base change functor's
--   maps, whose projections are canonical pullback lifts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean#L231-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean#L231-L256

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalCharts_complexBaseChangePullback
    (N : ℕ) (hN : 0<N) :
    let a := lpsOriginalIntegerNormalSchemeOverlapMap N hN false
    let b := lpsOriginalIntegerNormalSchemeOverlapMap N hN true
    let i := lpsOriginalIntegerNormalGluedChartMap N hN false
    let j := lpsOriginalIntegerNormalGluedChartMap N hN true
    let x := lpsOriginalIntegerNormalGluedToSpecZ N hN
    let t := Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ))
    let h := lpsOriginalIntegerNormalCharts_pullback N hN
    IsPullback
      (((Over.pullback t).map
        (QEC.Coding.AlgebraicGeometry.ChartBaseChange.firstOverlapOver a i x)).left)
      (((Over.pullback t).map
        (QEC.Coding.AlgebraicGeometry.ChartBaseChange.secondOverlapOver a b i j x h)).left)
      (((Over.pullback t).map
        (QEC.Coding.AlgebraicGeometry.ChartBaseChange.leftChartOver i x)).left)
      (((Over.pullback t).map
        (QEC.Coding.AlgebraicGeometry.ChartBaseChange.rightChartOver j x)).left) := by sorry
