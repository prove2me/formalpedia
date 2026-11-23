-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_twist_smul_mem_unitary
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.twist_smul_mem_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:06.099492+00:00
-- url     : https://prove2.me/theorems/ba78e93f-d040-4963-b1ba-9b75d5f3e96a
-- title:
--   HW: twist smul mem unitary
-- statement:
--   The HW construction uses the twist smul mem unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelTwist.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelTwist.lean#L50-L53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.HW.twist_smul_mem_unitary {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] {s : ℂ}
    (hs : star s * s = 1) {A : V →L[ℂ] V} (hA : A ∈ unitary (V →L[ℂ] V)) :
    s • A ∈ unitary (V →L[ℂ] V) := by sorry
