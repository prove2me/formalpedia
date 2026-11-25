-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mixedDiff_zero_4b76ed212846
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mixedDiff_zero_4b76ed212846
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:18.082094+00:00
-- url     : https://prove2.me/theorems/880a981c-11a3-407b-8746-f66964f7a64a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mixed Diff zero 4b76ed212846: P2 M Ground Theory Heights  Heights Numbers DVR mixed Diff zero 4b76ed212846
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mixed Diff zero 4b76ed212846 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mixed Diff zero 4b76ed212846 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsCN.lean#L287-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsCN.lean#L287-L295

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mixedDiff_zero_4b76ed212846 {K : Type*} {n : ℕ} (bs : Fin n → K → ℤ) :
    mixedDiff bs (0 : (K → ℤ) → ℤ) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mixedDiff_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mixedDiff_zero_4b76ed212846
