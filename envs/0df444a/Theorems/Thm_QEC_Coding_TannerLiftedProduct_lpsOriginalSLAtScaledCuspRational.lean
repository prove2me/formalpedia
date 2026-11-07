-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSLAtScaledCuspRational
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSLAtScaledCuspRational
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:12:17.262568+00:00
-- url     : https://prove2.me/theorems/ef816837-2137-4bed-816c-341372501fc2
-- title:
--   Tanner Lifted Product: lps Original SLAt Scaled Cusp Rational
-- statement:
--   Every actual integral SL branch has a positive affine slope at most N squared and a rational shift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L361-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L361-L379

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSLAtScaledCuspRational (N : ℕ) (hN : 0<N) (g : 𝒮ℒ) :
    ∃ m : ℕ, ∃ hm : 0<m, ∃ r : ℚ, m≤N^2 ∧ ∀ σ : ℍ,
      lpsOriginalJDilated N hN (g.val • (lpsE2AffineMatrix N hN 0 • σ))=
        lpsOriginalJInvariant (lpsE2AffineMatrix m hm (r:ℝ) • σ) := by sorry
