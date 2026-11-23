-- Prove2me | Theorems.Thm_SumProduct_zInfty_ofReal
-- name    : SumProduct.zInfty_ofReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:33:59.800018+00:00
-- url     : https://prove2.me/theorems/aaea4112-f43c-4ad7-a594-c6e9acfd8826
-- title:
--   Sum Product: z Infty of Real
-- statement:
--   **Realness of the archimedean factor.** For real `s`, `DedekindZeta.ZInfty K (s : ℂ)` is the
--   `ofReal` of sum_product's real prefactor
--   `|d|^{s/2} · (π^{-s/2}Γ(s/2))^{r₁} · (2(2π)^{-s}Γ(s))^{r₂}`.
--
--   PROOF PLAN (moderate): unfold `DedekindZeta.ZInfty`, `DedekindZeta.LReal`, `DedekindZeta.LComplex`.
--   Push `Complex.ofReal` through `Complex.ofReal_cpow` (bases `|d| ≥ 0`, `π ≥ 0`, `2π ≥ 0`), the real
--   exponents `-(s/2)`, `-s`, `s/2`, and `Complex.Gamma_ofReal` (`Complex.Gamma (s:ℂ) = (Real.Gamma s : ℂ)`,
--   valid since the arguments `s/2, s > 0`). The `(|discr K| : ℤ : ℂ) ^ (s/2)` matches sum_product's
--   `|(discr K : ℝ)| ^ (s/2)` via `Int.cast_abs`/`Complex.ofReal_intCast`. Note `-s/2 = -(s/2)`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L65-L101
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L65-L101

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Definitions.Def_SumProduct_PartialZetaMellin
set_option autoImplicit true
open scoped NumberField nonZeroDivisors
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open SumProduct
variable (K : Type*) [Field K] [NumberField K]

theorem SumProduct.zInfty_ofReal (s : ℝ) :
    DedekindZeta.ZInfty K (s : ℂ)
      = ((|(NumberField.discr K : ℝ)| ^ (s / 2)
          * (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ NumberField.InfinitePlace.nrRealPlaces K
          * (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s)
              ^ NumberField.InfinitePlace.nrComplexPlaces K : ℝ) : ℂ) := by sorry
