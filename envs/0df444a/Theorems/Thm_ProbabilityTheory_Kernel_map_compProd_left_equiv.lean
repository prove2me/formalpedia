-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_map_compProd_left_equiv
-- name    : ProbabilityTheory.Kernel.map_compProd_left_equiv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:42:54.445017+00:00
-- url     : https://prove2.me/theorems/2afc0b8b-14d0-4f60-90b3-62d24e74923a
-- title:
--   Map a kernel composition product along a measurable equivalence
-- statement:
--   Let $\kappa$ and $\eta$ be s-finite kernels and let $e$ be a measurable equivalence between the first-output spaces. Mapping their composition-product kernel along the first-coordinate equivalence agrees with mapping the first kernel and comapping the second along the inverse equivalence. Original Lean 4 theorem by Scott Armstrong; not a synthetic helper.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/CompProdReindex.lean#L23-L46

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.CompProd
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open ProbabilityTheory.Kernel

theorem ProbabilityTheory.Kernel.map_compProd_left_equiv
    {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (κ : Kernel X A) [IsSFiniteKernel κ]
    (η : Kernel (X × A) B) [IsSFiniteKernel η]
    (e : A ≃ᵐ C) :
    (κ ⊗ₖ η).map (Prod.map e id) =
      κ.map e ⊗ₖ η.comap
        (fun z : X × C ↦ (z.1, e.symm z.2))
        (measurable_fst.prodMk (e.symm.measurable.comp measurable_snd)) := by sorry
