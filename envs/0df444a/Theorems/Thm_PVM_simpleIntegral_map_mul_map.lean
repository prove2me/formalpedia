-- Prove2me | Theorems.Thm_PVM_simpleIntegral_map_mul_map
-- name    : PVM.simpleIntegral_map_mul_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:19.469912+00:00
-- url     : https://prove2.me/theorems/06d7604f-7b28-5bfa-a085-bee0332b0a6e
-- title:
--   PVM: simple Integral map mul map
-- statement:
--   On a fixed simple partition, pointwise multiplication becomes operator multiplication.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L153-L180
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L153-L180

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PVM.simpleIntegral_map_mul_map (E_pvm : PVM E) {β : Type*}
    (f : SimpleFunc ℝ β) (a b : β → ℂ) :
    E_pvm.simpleIntegral (f.map a) * E_pvm.simpleIntegral (f.map b) =
      E_pvm.simpleIntegral (f.map fun z => a z * b z) := by sorry
