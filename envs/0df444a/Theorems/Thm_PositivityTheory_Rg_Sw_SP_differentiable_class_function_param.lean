-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_differentiable_class_function_param
-- name    : PositivityTheory.Rg.Sw.SP.differentiable_class_function_param
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:15.857799+00:00
-- url     : https://prove2.me/theorems/ac17682d-893e-4766-9ab6-b6b0f73e22c5
-- title:
--   SP: differentiable class function param
-- statement:
--   The SP construction uses the differentiable class function param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DifferentiableClassFunctionParam.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DifferentiableClassFunctionParam.lean#L14-L17

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DifferentiableClassFunctionParam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.SP.differentiable_class_function_param (s : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (B : MC n) :
    Differentiable ℂ (fun z : ℂ => clsC s z p q R B) := by sorry
