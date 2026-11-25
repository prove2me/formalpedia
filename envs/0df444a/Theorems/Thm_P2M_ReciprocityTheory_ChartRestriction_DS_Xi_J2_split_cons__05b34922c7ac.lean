-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_J2_split_cons__05b34922c7ac
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_J2_split_cons__05b34922c7ac
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:12:29.0083+00:00
-- url     : https://prove2.me/theorems/a38b95dc-e347-4de2-91e1-65bab1f4b153
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi J2 split cons  05b34922c7ac: P2 M Reciprocity Theory Chart Restriction DS Xi J2 split cons  05b34922c7ac
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi J2 split cons  05b34922c7ac construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi J2 split cons  05b34922c7ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/VolumeUnivFinZero.lean#L127-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/VolumeUnivFinZero.lean#L127-L142

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_J2_split_cons__05b34922c7ac {p : ℕ} {R : Type*} [MeasureSpace R] [SFinite (volume : Measure R)]
    (G : (Fin (p + 1) → ℂ) × R → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ z, G z = ∫⁻ q : (Fin p → ℂ) × R, ∫⁻ w : ℂ, G (Fin.cons w q.1, q.2) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«J2».«split_cons'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_J2_split_cons__05b34922c7ac
