-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalE4NormalizedEquation_coeff_degree
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalE4NormalizedEquation_coeff_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:22:02.361402+00:00
-- url     : https://prove2.me/theorems/07f1a166-5293-43c0-9b9a-4f5007a7f6da
-- title:
--   Tanner Lifted Product: lps Original Reciprocal E4 Normalized Equation coeff degree
-- statement:
--   Sign normalization preserves the actual common inner-degree bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L142-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L142-L150

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalE4NormalizedEquation_coeff_degree
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) (n : ℕ) :
    ((lpsOriginalReciprocalE4NormalizedEquation N k A).coeff n).natDegree ≤
      k * Nat.card (LPSOriginalMeromorphicCosets N) := by sorry
