-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalScaleRootsCosetProduct
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalScaleRootsCosetProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:15:27.63722+00:00
-- url     : https://prove2.me/theorems/5f4107d7-7dee-44b3-9610-57a77c03bf52
-- title:
--   Tanner Lifted Product: lps Original Scale Roots Coset Product
-- statement:
--   Actual scaleRoots identity for the finite product of linear root factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L664-L673
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L664-L673

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalScaleRootsCosetProduct {ι : Type*}
    (s : Finset ι) (f : ι→ℂ) (r : ℂ) :
    (∏ i∈s, (Polynomial.X-Polynomial.C (f i))).scaleRoots r=
      ∏ i∈s, (Polynomial.X-Polynomial.C (f i*r)) := by sorry
