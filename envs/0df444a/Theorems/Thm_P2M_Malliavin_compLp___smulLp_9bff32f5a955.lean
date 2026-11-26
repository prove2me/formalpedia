-- Prove2me | Theorems.Thm_P2M_Malliavin_compLp___smulLp_9bff32f5a955
-- name    : P2M_Malliavin_compLp___smulLp_9bff32f5a955
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:30.874624+00:00
-- url     : https://prove2.me/theorems/13057910-7db3-460f-94a9-2e46fe5f4e16
-- title:
--   P2 M Malliavin comp Lp   smul Lp 9bff32f5a955: P2 M Malliavin comp Lp   smul Lp 9bff32f5a955
-- statement:
--   `compLpₗᵢ` is natural on rank-one elements.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L100-L105
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L100-L105

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

theorem P2M_Malliavin_compLp___smulLp_9bff32f5a955 (L : E →ₗᵢ[ℝ] F) (e : E) (G : Lp ℝ 2 μ) :
    compLpₗᵢ L (smulLp e G) = smulLp (L e) G := by sorry

alias «Malliavin».«compLpₗᵢ_smulLp» := P2M_Malliavin_compLp___smulLp_9bff32f5a955
