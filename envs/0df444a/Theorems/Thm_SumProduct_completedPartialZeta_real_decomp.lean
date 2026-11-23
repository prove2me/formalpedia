-- Prove2me | Theorems.Thm_SumProduct_completedPartialZeta_real_decomp
-- name    : SumProduct.completedPartialZeta_real_decomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:01:21.742921+00:00
-- url     : https://prove2.me/theorems/e9ef22ce-ce79-4fda-a5a1-1cb772114670
-- title:
--   Sum Product: completed Partial Zeta real decomp
-- statement:
--   **The clean real decomposition of dedekind's per-ideal completed zeta.** For real `s > 1`,
--
--       `(completedPartialZeta K 𝔞 (s:ℂ)).re = pf · (conePolarRe + tailRe)`,
--
--   with `pf = (1/w)·𝔑(𝔞)^s·|d|^{s/2}`, `conePolarRe = −V/s + (V/X)/(s−1)`,
--   and `tailRe = (mellinTail …).re`. Assembled from dedekind's
--   `completedPartialZeta_eq_conePolarCorrection_add_tail` and the realness lemmas above.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L244-L269
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L244-L269

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

theorem SumProduct.completedPartialZeta_real_decomp (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) {s : ℝ} (hs : 1 < s) :
    (DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ)).re
      = ((1 / (Units.torsionOrder K : ℝ))
            * (Ideal.absNorm 𝔞 : ℝ) ^ s
            * (|(NumberField.discr K : ℝ)|) ^ (s / 2))
        * ((- (surfaceVolume K).re / s
            + (1 / Theta.covolume K 𝔞) * (surfaceVolume K).re / (s - 1))
          + (mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
              (surfaceVolume K) (surfaceVolume K)
              ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 (s : ℂ)).re) := by sorry
