-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedScheme_noetherian
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedScheme_noetherian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:54:07.614858+00:00
-- url     : https://prove2.me/theorems/f99bed96-eec5-47f3-87c8-cae3782f418d
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued Scheme noetherian
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued Scheme noetherian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L377-L390
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L377-L390

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedScheme_noetherian
    (N : ℕ) [NeZero N] (hN : 0<N) :
    IsNoetherian (lpsOriginalIntegerNormalGluedScheme N hN) := by sorry
