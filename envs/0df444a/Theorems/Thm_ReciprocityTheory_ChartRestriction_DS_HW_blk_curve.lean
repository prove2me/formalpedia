-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_blk_curve
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.blk_curve
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:15.760387+00:00
-- url     : https://prove2.me/theorems/6800be18-ef18-4c63-90b8-9d81487581b9
-- title:
--   HW: blk curve
-- statement:
--   The HW construction uses the blk curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Blocks.lean#L204-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Blocks.lean#L204-L215

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.blk_curve {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (γ : ℝ → KG ε) (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X))
    (γp : ℝ → KG (fun _ : Fin (blkP ε true) => true))
    (hp : ∀ t : ℝ, toMK (γp t) = NormedSpace.exp ((t : ℂ) • blkRes ε true X))
    (γm : ℝ → KG (fun _ : Fin (blkP ε false) => true))
    (hm : ∀ t : ℝ, toMK (γm t) = NormedSpace.exp ((t : ℂ) • blkRes ε false X)) (t : ℝ) :
    γ t = blkEmbed ε true (γp t) * blkEmbed ε false (γm t) := by sorry
