-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lowComp_tensAct_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.lowComp_tensAct_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:42:10.468916+00:00
-- url     : https://prove2.me/theorems/93f0efbe-3f26-5eb6-ab09-6cc2941e87a4
-- title:
--   HW: low Comp tens Act apply
-- statement:
--   The HW construction uses the low Comp tens Act apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/LowComp.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/LowComp.lean#L14-L18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_LowComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem ReciprocityTheory.ChartRestriction.DS.HW.lowComp_tensAct_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*}
    [Fintype ι] {n : ℕ} (A : Fin n → Fin n → Module.End ℂ V) (M : Fin n → Fin n → Matrix ι ι ℂ)
    (a b : Fin n) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensAct A M a b x i = A a b (x i) + ∑ j, M a b i j • x j := by sorry
