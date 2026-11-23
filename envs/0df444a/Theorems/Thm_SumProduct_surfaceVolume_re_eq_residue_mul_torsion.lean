-- Prove2me | Theorems.Thm_SumProduct_surfaceVolume_re_eq_residue_mul_torsion
-- name    : SumProduct.surfaceVolume_re_eq_residue_mul_torsion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:01:36.811968+00:00
-- url     : https://prove2.me/theorems/33c8ba49-78bf-4692-b3b1-2c209e9aeb3f
-- title:
--   Sum Product: surface Volume re eq residue mul torsion
-- statement:
--   **The surface-volume ↔ regulator identity** (class-number-formula linchpin), in `.re` form:
--   `(surfaceVolume K).re = partialCompletedZetaResidue K · torsionOrder K`, equivalently `V = ρ·w`.
--
--   Proved by computing the residue of `completedDedekindZeta` at `s = 1` two ways and equating: the
--   geometric sum `classNumber · V/w` (`completedDedekindZeta_residue_geometric`) versus Mathlib's
--   analytic class number formula `Z_∞(1)·κ = (√|d|/π^{r₂})·dedekindZeta_residue`
--   (`completedDedekindZeta_eq` + `zInfty_one` + `tendsto_sub_one_mul_dedekindZeta_nhdsGT`), then the
--   elementary residue identity `(√|d|/π^{r₂})·κ = classNumber·ρ`; cancel `classNumber > 0`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L435-L566
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L435-L566

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

theorem SumProduct.surfaceVolume_re_eq_residue_mul_torsion :
    (surfaceVolume K).re = partialCompletedZetaResidue K * (Units.torsionOrder K : ℝ) := by sorry
