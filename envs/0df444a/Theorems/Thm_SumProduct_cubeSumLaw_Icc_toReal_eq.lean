-- Prove2me | Theorems.Thm_SumProduct_cubeSumLaw_Icc_toReal_eq
-- name    : SumProduct.cubeSumLaw_Icc_toReal_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:56:51.543799+00:00
-- url     : https://prove2.me/theorems/fccedfd1-6d59-494e-a224-81377332e30f
-- title:
--   Sum Product: cube Sum Law Icc to Real eq
-- statement:
--   The Sum Product construction uses the cube Sum Law Icc to Real eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L527-L537
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean#L527-L537

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section

theorem SumProduct.cubeSumLaw_Icc_toReal_eq (n : ℕ) :
    (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal =
      (volume (cubeSection (Fin n) 1)).toReal / (2 : ℝ) ^ n := by sorry
