-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_blkRes_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.blkRes_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:55.680261+00:00
-- url     : https://prove2.me/theorems/c50611a6-731d-4342-a596-261dc4189d80
-- title:
--   HW: blk Res apply
-- statement:
--   The HW construction uses the blk Res apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Blocks.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Blocks.lean#L34-L35

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.blkRes_apply (ε : Fin n → Bool) (s : Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin (blkP ε s)) : blkRes ε s X i j = X (blkSig ε ⟨s, i⟩) (blkSig ε ⟨s, j⟩) := by sorry
