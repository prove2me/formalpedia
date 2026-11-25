-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_metricDefect_smul_885c138dceb0
-- name    : P2M_GroundTheory_Heights__Heights_metricDefect_smul_885c138dceb0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:58.652953+00:00
-- url     : https://prove2.me/theorems/51927559-483c-4380-99a9-0f13a645cdd5
-- title:
--   P2 M Ground Theory Heights  Heights metric Defect smul 885c138dceb0: P2 M Ground Theory Heights  Heights metric Defect smul 885c138dceb0
-- statement:
--   The P2 M Ground Theory Heights  Heights metric Defect smul 885c138dceb0 construction uses the P2 M Ground Theory Heights  Heights metric Defect smul 885c138dceb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L18-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_metricDefect_smul_885c138dceb0 (A : HermLine n) (c : ι → ℂ) (z : Cone n ℂ) (hc : ∀ k, c k ≠ 0)
    (hz : BlockNonzero z) :
    metricDefect A (fun k i ↦ c k * z k i) = metricDefect A z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«metricDefect_smul» := P2M_GroundTheory_Heights__Heights_metricDefect_smul_885c138dceb0
