-- Prove2me | Theorems.Thm_P2M_Malliavin_compLp___boundedSMul_3f896ab5bcad
-- name    : P2M_Malliavin_compLp___boundedSMul_3f896ab5bcad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:11:20.834795+00:00
-- url     : https://prove2.me/theorems/6d1833de-5b24-5971-8efa-bf17d9561c4d
-- title:
--   P2 M Malliavin comp Lp   bounded SMul 3f896ab5bcad: P2 M Malliavin comp Lp   bounded SMul 3f896ab5bcad
-- statement:
--   Pointwise linear maps commute with bounded multipliers.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L81-L87
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L81-L87

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem P2M_Malliavin_compLp___boundedSMul_3f896ab5bcad (L : E →ₗᵢ[ℝ] F) {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ)
    {C : ℝ} (hC : ∀ x, |G x| ≤ C) (f : Lp E 2 μ) :
    compLpₗᵢ L (boundedSMul hG hC f) = boundedSMul hG hC (compLpₗᵢ L f) := by sorry

alias «Malliavin».«compLpₗᵢ_boundedSMul» := P2M_Malliavin_compLp___boundedSMul_3f896ab5bcad
