-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_differentiableOn_det_of
-- name    : ReciprocityTheory.MultiplicativeHeights.differentiableOn_det_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:03.045809+00:00
-- url     : https://prove2.me/theorems/b51a7dc5-267b-4ad4-a14c-eb24fc87e8b1
-- title:
--   Multiplicative Heights: differentiable On det of
-- statement:
--   The Multiplicative Heights construction uses the differentiable On det of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareDetA.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareDetA.lean#L33-L40

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix Filter Topology Set

theorem ReciprocityTheory.MultiplicativeHeights.differentiableOn_det_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Type} [Fintype U] [DecidableEq U] {F : U → U → E → ℂ} {B : Set E}
    (hF : ∀ a b, DifferentiableOn ℂ (F a b) B) :
    DifferentiableOn ℂ (fun v => (Matrix.of fun a b => F a b v).det) B := by sorry
