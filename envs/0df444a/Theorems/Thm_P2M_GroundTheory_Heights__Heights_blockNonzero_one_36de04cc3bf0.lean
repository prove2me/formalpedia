-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockNonzero_one_36de04cc3bf0
-- name    : P2M_GroundTheory_Heights__Heights_blockNonzero_one_36de04cc3bf0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:31.922318+00:00
-- url     : https://prove2.me/theorems/3421b74b-f7f5-438f-b4fc-f5946a477d62
-- title:
--   P2 M Ground Theory Heights  Heights block Nonzero one 36de04cc3bf0: P2 M Ground Theory Heights  Heights block Nonzero one 36de04cc3bf0
-- statement:
--   The P2 M Ground Theory Heights  Heights block Nonzero one 36de04cc3bf0 construction uses the P2 M Ground Theory Heights  Heights block Nonzero one 36de04cc3bf0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L151-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L151-L152

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
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
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_blockNonzero_one_36de04cc3bf0 : BlockNonzero (fun _ _ ↦ (1 : ℂ) : Cone n ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«blockNonzero_one» := P2M_GroundTheory_Heights__Heights_blockNonzero_one_36de04cc3bf0
