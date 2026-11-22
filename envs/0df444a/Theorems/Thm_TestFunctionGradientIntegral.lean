-- Prove2me | Theorems.Thm_TestFunctionGradientIntegral
-- name    : TestFunctionGradientIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:09:34.727808+00:00
-- url     : https://prove2.me/theorems/4132ab5b-14bd-4ef0-a6c1-74709d41dc2d
-- title:
--   Test Function Gradient Integral: Test Function Gradient Integral
-- statement:
--   The integral over the plane of the gradient of a compactly supported `C^1`
--   function vanishes.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TestFunctionGradientIntegral.lean#L12-L48
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TestFunctionGradientIntegral.lean#L12-L48

import Definitions.Def_PHigherOrder_Plane
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_PHigherOrder_TestFunctionGradientIntegral
set_option autoImplicit false

theorem TestFunctionGradientIntegral (φ : Plane → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) :
    ∫ x : Plane, gradient φ x = 0 := by sorry
