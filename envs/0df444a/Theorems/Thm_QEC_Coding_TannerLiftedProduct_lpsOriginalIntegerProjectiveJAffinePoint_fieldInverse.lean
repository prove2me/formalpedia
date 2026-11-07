-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJAffinePoint_fieldInverse
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJAffinePoint_fieldInverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:02:44.113959+00:00
-- url     : https://prove2.me/theorems/0031336c-348a-438f-9d89-fa079de6ba03
-- title:
--   Tanner Lifted Product: lps Original Integer Projective JAffine Point field Inverse
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Projective JAffine Point field Inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L994-L998
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L994-L998

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJAffinePoint_fieldInverse
    (K : Type) [Field K] (x : K) (hx : x≠0) :
    lpsOriginalIntegerProjectiveJAffinePoint K false x =
      lpsOriginalIntegerProjectiveJAffinePoint K true x⁻¹ := by sorry
