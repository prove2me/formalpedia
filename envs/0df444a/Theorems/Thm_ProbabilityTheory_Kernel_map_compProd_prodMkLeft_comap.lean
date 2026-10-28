-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_map_compProd_prodMkLeft_comap
-- name    : ProbabilityTheory.Kernel.map_compProd_prodMkLeft_comap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:42:54.151983+00:00
-- url     : https://prove2.me/theorems/d8d8a81c-5566-4da7-98b0-db0b7b05fa68
-- title:
--   Compatible coordinate maps commute with kernel composition product
-- statement:
--   For s-finite kernels and compatible measurable terminal statistics, mapping both coordinates of a composition product commutes with the corresponding pushforward and pullback operations on its kernel factors. Original Lean 4 theorem by Scott Armstrong; not a synthetic helper.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/CompProdReindex.lean#L68-L95

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.CompProd
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open ProbabilityTheory.Kernel

theorem ProbabilityTheory.Kernel.map_compProd_prodMkLeft_comap
    {X A B C D T : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace T]
    (κ : Kernel X A) [IsSFiniteKernel κ]
    (η : Kernel T B) [IsSFiniteKernel η]
    (terminal : A → T)
    (terminal' : C → T) (hterminal' : Measurable terminal')
    (f : A → C) (hf : Measurable f) (g : B → D) (hg : Measurable g)
    (hcompat : terminal' ∘ f = terminal) :
    (κ ⊗ₖ Kernel.prodMkLeft X
      (η.comap terminal (hcompat ▸ hterminal'.comp hf))).map (Prod.map f g) =
      κ.map f ⊗ₖ
        Kernel.prodMkLeft X ((η.map g).comap terminal' hterminal') := by sorry
