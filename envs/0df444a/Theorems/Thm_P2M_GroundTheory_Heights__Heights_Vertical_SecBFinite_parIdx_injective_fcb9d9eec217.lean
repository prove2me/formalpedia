-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_parIdx_injective_fcb9d9eec217
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_parIdx_injective_fcb9d9eec217
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:46.534805+00:00
-- url     : https://prove2.me/theorems/ef4cc7ff-d8bd-43b3-8248-49411409068c
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite par Idx injective fcb9d9eec217: P2 M Ground Theory Heights  Heights Vertical Sec BFinite par Idx injective fcb9d9eec217
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite par Idx injective fcb9d9eec217 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite par Idx injective fcb9d9eec217 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L193-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L193-L195

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_parIdx_injective_fcb9d9eec217 (e n : ℕ) : Function.Injective (parIdx e n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«parIdx_injective» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_parIdx_injective_fcb9d9eec217
