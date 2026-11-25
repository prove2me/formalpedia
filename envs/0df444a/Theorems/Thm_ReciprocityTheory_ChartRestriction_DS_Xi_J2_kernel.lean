-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_kernel
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.J2.kernel
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:08.966271+00:00
-- url     : https://prove2.me/theorems/6ea9d7ac-953d-5609-b027-e905399d1805
-- title:
--   J2: kernel
-- statement:
--   The J2 construction uses the kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/VolumeUnivFinZero.lean#L43-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/VolumeUnivFinZero.lean#L43-L91

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.J2.kernel (Q D : ℝ) (hQ : 0 < Q) (hD : 0 < D) (c : ℂ) (s : ℝ) :
    ∫⁻ w : ℂ, ENNReal.ofReal ((Q * ‖w - c‖ ^ 2 + D) ^ (-s / 2)) =
      ENNReal.ofReal (Q⁻¹ * D ^ (1 - s / 2)) * kc s := by sorry
