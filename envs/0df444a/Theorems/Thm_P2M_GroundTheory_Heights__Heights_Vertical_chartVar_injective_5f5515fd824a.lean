-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_chartVar_injective_5f5515fd824a
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_chartVar_injective_5f5515fd824a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:43:13.751875+00:00
-- url     : https://prove2.me/theorems/86a954fc-080e-4b2c-b497-5df0093fa019
-- title:
--   P2 M Ground Theory Heights  Heights Vertical chart Var injective 5f5515fd824a: P2 M Ground Theory Heights  Heights Vertical chart Var injective 5f5515fd824a
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical chart Var injective 5f5515fd824a construction uses the P2 M Ground Theory Heights  Heights Vertical chart Var injective 5f5515fd824a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L18-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormIdentity
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
variable {K : Type*} [Field K] [NumberField K] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_chartVar_injective_5f5515fd824a (e n : ℕ) : Function.Injective (chartVar e n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«chartVar_injective» := P2M_GroundTheory_Heights__Heights_Vertical_chartVar_injective_5f5515fd824a
