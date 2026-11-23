-- Prove2me | Theorems.Thm_SumProduct_zInfty_one
-- name    : SumProduct.zInfty_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:00:52.492961+00:00
-- url     : https://prove2.me/theorems/e433e0b6-6031-4802-ac7d-d8ba188c091c
-- title:
--   Sum Product: z Infty one
-- statement:
--   **`Z_∞` at `s = 1`.** `DedekindZeta.ZInfty K 1 = (√|d| / π^{r₂} : ℂ)`.
--
--   PROOF PLAN (moderate): unfold `ZInfty`/`LReal`/`LComplex` at `s = 1`.
--   `(|d| : ℂ)^(1/2) = √|d|` (`Complex.ofReal_cpow` + `Real.rpow_half`/`Real.sqrt_eq_rpow`).
--   `LReal 1 = π^{-1/2} Γ(1/2) = 1`: use `Complex.Gamma_one_half_eq` (`Γ(1/2) = √π`) and
--   `π^{-1/2} = (√π)⁻¹`. `LComplex 1 = 2·(2π)^{-1}·Γ 1 = 2/(2π) = 1/π`: `Complex.Gamma_one = 1`.
--   So `ZInfty 1 = √|d| · 1^{r₁} · (1/π)^{r₂} = √|d| / π^{r₂}`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L117-L139
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L117-L139

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Definitions.Def_SumProduct_PartialZetaMellin
set_option autoImplicit true
open scoped NumberField nonZeroDivisors
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open SumProduct
variable (K : Type*) [Field K] [NumberField K]

theorem SumProduct.zInfty_one :
    DedekindZeta.ZInfty K (1 : ℂ)
      = ((Real.sqrt |(NumberField.discr K : ℝ)|
          / Real.pi ^ NumberField.InfinitePlace.nrComplexPlaces K : ℝ) : ℂ) := by sorry
