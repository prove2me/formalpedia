-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_sum_add_pi_single_one_3a9c5801f689
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_sum_add_pi_single_one_3a9c5801f689
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:24:39.589711+00:00
-- url     : https://prove2.me/theorems/bfc30713-929d-4e0a-9f57-9b1426192f99
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel sum add pi single one 3a9c5801f689: P2 M Ground Theory Heights  Heights Hilbert Samuel sum add pi single one 3a9c5801f689
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel sum add pi single one 3a9c5801f689 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel sum add pi single one 3a9c5801f689 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegLTGrowth.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegLTGrowth.lean#L46-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.NumbersDVR
variable {K : Type} [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_sum_add_pi_single_one_3a9c5801f689 (m : K → ℕ) (k : K) :
    ∑ j, (m + Pi.single k 1 : K → ℕ) j = ∑ j, m j + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«sum_add_pi_single_one» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_sum_add_pi_single_one_3a9c5801f689
