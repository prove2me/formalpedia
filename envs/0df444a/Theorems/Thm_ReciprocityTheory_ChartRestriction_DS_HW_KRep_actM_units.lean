-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KRep_actM_units
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.KRep.actM_units
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:11.947223+00:00
-- url     : https://prove2.me/theorems/7821c333-5541-5eae-bd77-820afcdb3fca
-- title:
--   KRep: act M units
-- statement:
--   The KRep construction uses the act M units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/URepCompRedOf.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/URepCompRedOf.lean#L25-L32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_URepCompRedOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.HW.KRep.actM_units {ε : Fin n → Bool} (R : KRep ε) (X : Matrix (Fin n) (Fin n) ℂ) (v : R.V) :
    actM R.units X v = R.dτ X v := by sorry
