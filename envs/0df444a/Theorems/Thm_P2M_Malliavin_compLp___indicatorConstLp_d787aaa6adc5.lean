-- Prove2me | Theorems.Thm_P2M_Malliavin_compLp___indicatorConstLp_d787aaa6adc5
-- name    : P2M_Malliavin_compLp___indicatorConstLp_d787aaa6adc5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:47.465664+00:00
-- url     : https://prove2.me/theorems/75bb83bf-a710-4038-8bb2-732b811f1e39
-- title:
--   P2 M Malliavin comp Lp   indicator Const Lp d787aaa6adc5: P2 M Malliavin comp Lp   indicator Const Lp d787aaa6adc5
-- statement:
--   The P2 M Malliavin comp Lp   indicator Const Lp d787aaa6adc5 construction uses the P2 M Malliavin comp Lp   indicator Const Lp d787aaa6adc5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L89-L97
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L89-L97

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

theorem P2M_Malliavin_compLp___indicatorConstLp_d787aaa6adc5 (L : E →ₗᵢ[ℝ] F) {A : Set Ω} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) (c : E) :
    compLpₗᵢ L (indicatorConstLp 2 hA hμA c) = indicatorConstLp 2 hA hμA (L c) := by sorry

alias «Malliavin».«compLpₗᵢ_indicatorConstLp» := P2M_Malliavin_compLp___indicatorConstLp_d787aaa6adc5
