-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_MultiplicativeHeights_differentiableOn_finset_prod__599928e8b47e
-- name    : P2M_ReciprocityTheory_MultiplicativeHeights_differentiableOn_finset_prod__599928e8b47e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:17:43.683905+00:00
-- url     : https://prove2.me/theorems/ae3eddf0-591d-4afb-9c71-a06897db507a
-- title:
--   P2 M Reciprocity Theory Multiplicative Heights differentiable On finset prod  599928e8b47e: P2 M Reciprocity Theory Multiplicative Heights differentiable On finset prod  599928e8b47e
-- statement:
--   The P2 M Reciprocity Theory Multiplicative Heights differentiable On finset prod  599928e8b47e construction uses the P2 M Reciprocity Theory Multiplicative Heights differentiable On finset prod  599928e8b47e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareDetA.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareDetA.lean#L23-L31

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

theorem P2M_ReciprocityTheory_MultiplicativeHeights_differentiableOn_finset_prod__599928e8b47e {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [DecidableEq ι] {F : ι → E → ℂ} {B : Set E}
    (hF : ∀ i, DifferentiableOn ℂ (F i) B) (s : Finset ι) :
    DifferentiableOn ℂ (fun v => ∏ i ∈ s, F i v) B := by sorry

alias «ReciprocityTheory».«MultiplicativeHeights».«differentiableOn_finset_prod'» := P2M_ReciprocityTheory_MultiplicativeHeights_differentiableOn_finset_prod__599928e8b47e
