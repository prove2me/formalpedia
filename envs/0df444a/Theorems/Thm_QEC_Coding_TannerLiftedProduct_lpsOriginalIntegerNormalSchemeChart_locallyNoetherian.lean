-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalSchemeChart_locallyNoetherian
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSchemeChart_locallyNoetherian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:58:42.626071+00:00
-- url     : https://prove2.me/theorems/dba4e017-23cf-4dd6-aae6-065fb26fdf77
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Scheme Chart locally Noetherian
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Scheme Chart locally Noetherian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L358-L375
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L358-L375

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSchemeChart_locallyNoetherian
    (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool) :
    IsLocallyNoetherian (lpsOriginalIntegerNormalSchemeChart N hN b) := by sorry
