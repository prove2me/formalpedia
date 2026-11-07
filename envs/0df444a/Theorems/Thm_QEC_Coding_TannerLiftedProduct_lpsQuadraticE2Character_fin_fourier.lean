-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_fin_fourier
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Character_fin_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:48:49.738975+00:00
-- url     : https://prove2.me/theorems/ab036d8f-92b4-411a-a5fe-1988044533a4
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Character fin fourier
-- statement:
--   The finite residue representatives give the same actual character Fourier transform.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L100-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L100-L113

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Character_fin_fourier (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    (∑ a : Fin q, lpsQuadraticE2Character q (a.val:ZMod q) *
      ZMod.stdAddChar ((((a.val:ℤ)*(n:ℤ)):ℤ):ZMod q)) =
      lpsQuadraticE2Character q (n:ZMod q) *
        gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)) := by sorry
