-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_linForm_mem_integralModel_9dcb33b61818
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_linForm_mem_integralModel_9dcb33b61818
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:43:27.032824+00:00
-- url     : https://prove2.me/theorems/a83c3421-fb44-4831-9787-90ae19221c09
-- title:
--   P2 M Ground Theory Heights  Heights Vertical lin Form mem integral Model 9dcb33b61818: P2 M Ground Theory Heights  Heights Vertical lin Form mem integral Model 9dcb33b61818
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical lin Form mem integral Model 9dcb33b61818 construction uses the P2 M Ground Theory Heights  Heights Vertical lin Form mem integral Model 9dcb33b61818 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PVertSpec.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PVertSpec.lean#L51-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PVertSpec
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
variable {K : Type*} [Field K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_linForm_mem_integralModel_9dcb33b61818 {I : Ideal (MvPolynomial (Fin n) K)} {u : Fin n → 𝓞 K}
    (h : linForm u ∈ integralModel I) : linForm (fun j => (u j : K)) ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«linForm_mem_integralModel» := P2M_GroundTheory_Heights__Heights_Vertical_linForm_mem_integralModel_9dcb33b61818
