-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_eq_of_germ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_eq_of_germ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:15:36.918203+00:00
-- url     : https://prove2.me/theorems/9d83089f-077f-4716-9a00-b83e02515661
-- title:
--   Tanner Lifted Product: lps Original Taylor Series eq of germ
-- statement:
--   Equal analytic germs have equal actual Taylor series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L684-L692
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L684-L692

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_eq_of_germ {f g : ℂ→ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hfg : f=ᶠ[nhds 0]g) : lpsOriginalTaylorSeries f=lpsOriginalTaylorSeries g := by sorry
