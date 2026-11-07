-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJAffinePoint_toSpecZ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJAffinePoint_toSpecZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:02:50.075051+00:00
-- url     : https://prove2.me/theorems/af7c3ec0-d223-4af6-8004-36af5e7843a5
-- title:
--   Tanner Lifted Product: lps Original Integer Projective JAffine Point to Spec Z
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Projective JAffine Point to Spec Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L1007-L1012
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L1007-L1012

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJAffinePoint_toSpecZ
    (R : Type) [CommRing R] (b : Bool) (x : R) :
    lpsOriginalIntegerProjectiveJAffinePoint R b x ≫
      lpsOriginalIntegerProjectiveJLineToSpecZ =
    Spec.map (CommRingCat.ofHom (Int.castRingHom R)) := by sorry
