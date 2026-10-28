-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_map_compProd_prodMkLeft_right
-- name    : ProbabilityTheory.Kernel.map_compProd_prodMkLeft_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:42:53.589311+00:00
-- url     : https://prove2.me/theorems/ac1966a5-b160-4daa-bffc-910826c2b945
-- title:
--   Mapping the right factor commutes with kernel composition product
-- statement:
--   Let $\kappa$ and $\eta$ be s-finite kernels and let $f$ be a measurable map on the second factor. Mapping the second coordinate of the composite-product kernel equals first mapping the second kernel and then forming the composite product. Original Lean 4 theorem by Scott Armstrong; not a synthetic helper.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/CompProdReindex.lean#L48-L66

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.CompProd
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open ProbabilityTheory.Kernel

theorem ProbabilityTheory.Kernel.map_compProd_prodMkLeft_right
    {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (κ : Kernel X A) [IsSFiniteKernel κ]
    (η : Kernel A B) [IsSFiniteKernel η]
    (f : B → C) (hf : Measurable f) :
    (κ ⊗ₖ Kernel.prodMkLeft X η).map (fun z ↦ (z.1, f z.2)) =
      κ ⊗ₖ Kernel.prodMkLeft X (η.map f) := by sorry
