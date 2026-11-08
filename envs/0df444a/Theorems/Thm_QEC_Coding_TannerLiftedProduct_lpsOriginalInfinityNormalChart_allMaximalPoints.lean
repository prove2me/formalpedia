-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityNormalChart_allMaximalPoints
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityNormalChart_allMaximalPoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:09:52.434908+00:00
-- url     : https://prove2.me/theorems/6ed6df70-d848-43dc-81b1-5696159583ca
-- title:
--   Tanner Lifted Product: lps Original Infinity Normal Chart all Maximal Points
-- statement:
--   Every maximal ideal of the same original reciprocal integral closure is an existing actual infinity evaluation kernel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityPointCoverage.lean#L31-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityPointCoverage.lean#L31-L93

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityPoleClearingAway
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_PolynomialMaximalPoints
import Mathlib.RingTheory.Ideal.GoingUp
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityPointCoverage
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityPointCoverageDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityPointCoverageDictionary002
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityNormalChart_allMaximalPoints (M : Ideal R) [M.IsMaximal] :
    ∃ x : S, M = RingHom.ker
      (lpsOriginalInfinityNormalChartEvaluation N hpos hN x.val x.property) := by sorry
