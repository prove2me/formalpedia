-- Prove2me | Theorems.Thm_SumProduct_completedPartialZeta_residue_perIdeal
-- name    : SumProduct.completedPartialZeta_residue_perIdeal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:01:22.409819+00:00
-- url     : https://prove2.me/theorems/11864605-c4ce-4faa-b3ef-588f62b725e8
-- title:
--   Sum Product: completed Partial Zeta residue per Ideal
-- statement:
--   **Per-ideal completed-zeta residue at `s = 1` is `V/w`.** For any nonzero ideal `𝔞`,
--   `(s−1)·completedPartialZeta K 𝔞 (s:ℂ) → (surfaceVolume K)/(torsionOrder K)` as real `s → 1⁺`.
--   The prefactor `pf(s)=(1/w)·𝔑(𝔞)^s·|d|^{s/2}` is continuous with `pf(1)·(covolume K 𝔞)⁻¹ = 1/w`,
--   the cone correction contributes residue `(covolume)⁻¹·V` (`conePolarCorrection_residue_one`), and
--   the analytic `mellinTail` contributes `0`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L285-L396
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L285-L396

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

theorem SumProduct.completedPartialZeta_residue_perIdeal (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (surfaceVolume K / (Units.torsionOrder K : ℂ))) := by sorry
