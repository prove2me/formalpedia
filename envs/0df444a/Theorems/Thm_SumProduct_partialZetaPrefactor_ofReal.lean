-- Prove2me | Theorems.Thm_SumProduct_partialZetaPrefactor_ofReal
-- name    : SumProduct.partialZetaPrefactor_ofReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:00:57.923691+00:00
-- url     : https://prove2.me/theorems/23129b1c-0845-48a1-9cf2-3cd98bc91449
-- title:
--   Sum Product: partial Zeta Prefactor of Real
-- statement:
--   **The dedekind prefactor is `ofReal` of a positive real for real `s`.**
--   `(1/w)·(𝔑 𝔞)^s·|d|^{s/2} = ((1/w)·𝔑(𝔞)^s·|d|^{s/2} : ℝ)`, with the real value positive for `𝔞 ≠ 0`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L205-L218
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L205-L218

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

theorem SumProduct.partialZetaPrefactor_ofReal (𝔞 : Ideal (𝓞 K)) (s : ℝ) :
    (1 / (Units.torsionOrder K : ℂ)) * (Ideal.absNorm 𝔞 : ℂ) ^ (s : ℂ)
        * (((|NumberField.discr K| : ℤ) : ℂ) ^ ((s : ℂ) / 2))
      = (((1 / (Units.torsionOrder K : ℝ)) * (Ideal.absNorm 𝔞 : ℝ) ^ s
          * (|(NumberField.discr K : ℝ)|) ^ (s / 2) : ℝ) : ℂ) := by sorry
