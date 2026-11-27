-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockForms_isFormSystem_13915fe0a620
-- name    : P2M_GroundTheory_Heights__Heights_blockForms_isFormSystem_13915fe0a620
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:21.766107+00:00
-- url     : https://prove2.me/theorems/da0d47dc-2f18-41a5-8ffe-2a368e73701e
-- title:
--   P2 M Ground Theory Heights  Heights block Forms is Form System 13915fe0a620: P2 M Ground Theory Heights  Heights block Forms is Form System 13915fe0a620
-- statement:
--   The P2 M Ground Theory Heights  Heights block Forms is Form System 13915fe0a620 construction uses the P2 M Ground Theory Heights  Heights block Forms is Form System 13915fe0a620 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L78-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L78-L94

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

theorem P2M_GroundTheory_Heights__Heights_blockForms_isFormSystem_13915fe0a620 : (blockAddData n k₀).IsFormSystem 1 (blockForms n k₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«blockForms_isFormSystem» := P2M_GroundTheory_Heights__Heights_blockForms_isFormSystem_13915fe0a620
