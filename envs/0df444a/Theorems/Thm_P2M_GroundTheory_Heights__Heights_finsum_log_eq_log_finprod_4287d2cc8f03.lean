-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_log_eq_log_finprod_4287d2cc8f03
-- name    : P2M_GroundTheory_Heights__Heights_finsum_log_eq_log_finprod_4287d2cc8f03
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:05:28.111008+00:00
-- url     : https://prove2.me/theorems/6396b7b6-efb2-44cc-8438-952e64b30e6a
-- title:
--   P2 M Ground Theory Heights  Heights finsum log eq log finprod 4287d2cc8f03: P2 M Ground Theory Heights  Heights finsum log eq log finprod 4287d2cc8f03
-- statement:
--   The P2 M Ground Theory Heights  Heights finsum log eq log finprod 4287d2cc8f03 construction uses the P2 M Ground Theory Heights  Heights finsum log eq log finprod 4287d2cc8f03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L117-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L117-L127

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
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
open NumberField Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem P2M_GroundTheory_Heights__Heights_finsum_log_eq_log_finprod_4287d2cc8f03 {α : Type*} {f : α → ℝ} (hpos : ∀ a, 0 < f a)
    (hf : Function.HasFiniteMulSupport f) : ∑ᶠ a, Real.log (f a) = Real.log (∏ᶠ a, f a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finsum_log_eq_log_finprod» := P2M_GroundTheory_Heights__Heights_finsum_log_eq_log_finprod_4287d2cc8f03
