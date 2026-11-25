-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_exists_C_mul_mem_4f0656e53394
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_exists_C_mul_mem_4f0656e53394
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:42:37.915797+00:00
-- url     : https://prove2.me/theorems/048c1fbe-68a5-4f8f-94cd-ecc21fd3976b
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite exists C mul mem 4f0656e53394: P2 M Ground Theory Heights  Heights Vertical Sec BFinite exists C mul mem 4f0656e53394
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite exists C mul mem 4f0656e53394 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite exists C mul mem 4f0656e53394 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L157-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L157-L169

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
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_exists_C_mul_mem_4f0656e53394 {σ : Type*} (J : Ideal (MvPolynomial σ (𝓞 K))) (h : MvPolynomial σ (𝓞 K))
    (hh : MvPolynomial.map (algebraMap (𝓞 K) K) h ∈ J.map (MvPolynomial.map (algebraMap (𝓞 K) K))) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ C d * h ∈ J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«exists_C_mul_mem» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_exists_C_mul_mem_4f0656e53394
