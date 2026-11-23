-- Prove2me | Theorems.Thm_SumProduct_completedDedekindZeta_residue_geometric
-- name    : SumProduct.completedDedekindZeta_residue_geometric
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:01:27.266999+00:00
-- url     : https://prove2.me/theorems/828453bf-9b8c-47aa-b2af-61e1136a2e59
-- title:
--   Sum Product: completed Dedekind Zeta residue geometric
-- statement:
--   **Geometric total residue.** Summing the per-ideal residue over the class group:
--   `(s−1)·completedDedekindZeta K (s:ℂ) → (classNumber K)·V/w` as real `s → 1⁺`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L400-L425
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L400-L425

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

theorem SumProduct.completedDedekindZeta_residue_geometric :
    Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * DedekindZeta.completedDedekindZeta K (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((Fintype.card (ClassGroup (𝓞 K)) : ℂ) * (surfaceVolume K / (Units.torsionOrder K : ℂ))))
      := by sorry
