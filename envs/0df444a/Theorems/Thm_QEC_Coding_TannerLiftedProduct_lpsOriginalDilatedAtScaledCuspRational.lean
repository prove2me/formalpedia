-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDilatedAtScaledCuspRational
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDilatedAtScaledCuspRational
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:12:00.816676+00:00
-- url     : https://prove2.me/theorems/d60cc41c-ac98-47ec-b516-ad72c8af3c89
-- title:
--   Tanner Lifted Product: lps Original Dilated At Scaled Cusp Rational
-- statement:
--   Integral Bezout matrix reduction proves a rational affine cusp shift for the SAME original branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L259-L358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L259-L358

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDilatedAtScaledCuspRational (N : ℕ) (hN : 0<N) (γ : SL(2,ℤ)) :
    ∃ r : ℚ, ∀ σ : ℍ,
      lpsOriginalJDilated N hN (γ • (lpsE2AffineMatrix N hN 0 • σ))=
        lpsOriginalJInvariant
          (lpsE2AffineMatrix ((Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0))^2)
            (pow_pos (lpsOriginalDilationColumnGcdPos N hN γ) 2) (r:ℝ) • σ) := by sorry
