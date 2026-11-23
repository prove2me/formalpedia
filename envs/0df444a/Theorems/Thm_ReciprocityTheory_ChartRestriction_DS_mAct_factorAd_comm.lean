-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mAct_factorAd_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.mAct_factorAd_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:50.301805+00:00
-- url     : https://prove2.me/theorems/358eb275-0299-4756-bc29-9f96d41a213a
-- title:
--   DS: m Act factor Ad comm
-- statement:
--   The DS construction uses the m Act factor Ad comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L58-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
variable {E : Fin n → Fin n → Module.End ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.mAct_factorAd_comm (k : ℕ) (i : Fin k) (a b c d : Fin n) :
    mAct E k a b * factorAd k i c d = factorAd k i c d * mAct E k a b := by sorry
