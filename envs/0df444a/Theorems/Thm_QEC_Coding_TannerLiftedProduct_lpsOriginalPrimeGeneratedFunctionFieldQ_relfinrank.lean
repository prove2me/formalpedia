-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:15:51.086201+00:00
-- url     : https://prove2.me/theorems/5cdf10fe-7478-47df-b7e5-8b0f6d8f61fc
-- title:
--   Tanner Lifted Product: lps Original Prime Generated Function Field Q relfinrank
-- statement:
--   The same original coprime-prime function-field extension has degree p+1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L785-L795
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L785-L795

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N) (hN : 4 ∣ N)
    (hposN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hposN).relfinrank
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hposN (Fact.out : p.Prime).pos)) = p+1 := by sorry
