-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJLine_noetherian
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJLine_noetherian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:55:53.834738+00:00
-- url     : https://prove2.me/theorems/4920f8f8-608e-4eb0-92f0-77426016586c
-- title:
--   Tanner Lifted Product: lps Original Integer Projective JLine noetherian
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Projective JLine noetherian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L392-L402
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L392-L402

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJLine_noetherian :
    IsNoetherian lpsOriginalIntegerProjectiveJLine := by sorry
