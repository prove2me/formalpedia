-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_blkSig_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.blkSig_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:03:56.328128+00:00
-- url     : https://prove2.me/theorems/497c1115-3de3-4d4a-8368-9e0482f0fbca
-- title:
--   HW: blk Sig apply
-- statement:
--   The HW construction uses the blk Sig apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Blocks.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Blocks.lean#L22-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.HW.blkSig_apply (ε : Fin n → Bool) (s : Bool) (i : Fin (blkP ε s)) :
    blkSig ε ⟨s, i⟩ = (blkE ε s i : Fin n) := by sorry
