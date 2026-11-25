-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exp_blkDiag
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.exp_blkDiag
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:06.641587+00:00
-- url     : https://prove2.me/theorems/ecd53631-4ea8-43ca-b196-c683f48b7ee8
-- title:
--   HW: exp blk Diag
-- statement:
--   The HW construction uses the exp blk Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Blocks.lean#L180-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Blocks.lean#L180-L193

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.exp_blkDiag (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :
    NormedSpace.exp (blkDiag ε v) = blkDiag ε (fun s => NormedSpace.exp (v s)) := by sorry
