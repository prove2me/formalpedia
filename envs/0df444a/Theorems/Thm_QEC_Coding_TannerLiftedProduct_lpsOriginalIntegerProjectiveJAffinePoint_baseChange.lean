-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJAffinePoint_baseChange
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJAffinePoint_baseChange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:57:29.208355+00:00
-- url     : https://prove2.me/theorems/e4dbcba7-6da7-46b7-b6ba-062cf89bdcc4
-- title:
--   Tanner Lifted Product: lps Original Integer Projective JAffine Point base Change
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Projective JAffine Point base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L957-L968
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L957-L968

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJAffinePoint_baseChange
    (R K : Type) [CommRing R] [CommRing K] [Algebra R K] (b : Bool) (x : R) :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      lpsOriginalIntegerProjectiveJAffinePoint R b x =
    lpsOriginalIntegerProjectiveJAffinePoint K b (algebraMap R K x) := by sorry
