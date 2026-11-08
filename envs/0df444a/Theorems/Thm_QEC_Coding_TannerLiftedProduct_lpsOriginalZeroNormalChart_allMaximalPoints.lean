-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroNormalChart_allMaximalPoints
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalZeroNormalChart_allMaximalPoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:14:12.11022+00:00
-- url     : https://prove2.me/theorems/8f984f8e-cb11-42ed-b3fb-7ac44616e05d
-- title:
--   Tanner Lifted Product: lps Original Zero Normal Chart all Maximal Points
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Zero Normal Chart all Maximal Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroPointCoverage.lean#L41-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroPointCoverage.lean#L41-L103

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_PolynomialMaximalPoints
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPoleClearingAway
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
import Mathlib.RingTheory.Ideal.GoingUp
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroPointCoverage
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_interior_order_nonnegative

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroCoverageDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroCoverageDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroCoverageDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroCoverageDictionary004
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalZeroNormalChart_allMaximalPoints (M : Ideal R) [M.IsMaximal] :
    ∃ x : Q, M = RingHom.ker (lpsOriginalZeroNormalChartEvaluation N hpos hN (Sum.inl x)
      (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x)) := by sorry
