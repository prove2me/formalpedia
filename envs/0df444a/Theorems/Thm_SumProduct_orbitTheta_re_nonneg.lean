-- Prove2me | Theorems.Thm_SumProduct_orbitTheta_re_nonneg
-- name    : SumProduct.orbitTheta_re_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:00:47.533803+00:00
-- url     : https://prove2.me/theorems/4c559239-9893-46ca-bec0-22cc5d4020ed
-- title:
--   Sum Product: orbit Theta re nonneg
-- statement:
--   **`orbitTheta` is real and nonnegative.** The orbit-integrated theta `orbitTheta K 𝔞 r` is the
--   surface integral of `Theta.idealThetaKernel`, which is `Complex.ofReal` of a `tsum` of the
--   nonnegative Minkowski Gaussian (`DedekindZeta.mixedGaussian_nonneg`); hence it is real with
--   nonnegative real part.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L170-L183
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L170-L183

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Definitions.Def_SumProduct_PartialZetaMellin
set_option autoImplicit true
open scoped NumberField nonZeroDivisors
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open SumProduct
variable (K : Type*) [Field K] [NumberField K]
open DedekindZeta DedekindZeta.ConeRadialReduction DedekindZeta.ConeMellinBridge
  DedekindZeta.MellinPrinciple
open scoped nonZeroDivisors
variable {K}

theorem SumProduct.orbitTheta_re_nonneg (𝔞 : Ideal (𝓞 K)) (r : ℝ) :
    (orbitTheta K 𝔞 r).im = 0 ∧ 0 ≤ (orbitTheta K 𝔞 r).re := by sorry
