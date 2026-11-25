-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_eq_zero_of_forall_psi_85d62bcfb82e
-- name    : P2M_GroundTheory_Heights__Heights_KRest_eq_zero_of_forall_psi_85d62bcfb82e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:58.463802+00:00
-- url     : https://prove2.me/theorems/6b8f0fad-09d0-491e-985c-9c7916ce286c
-- title:
--   P2 M Ground Theory Heights  Heights KRest eq zero of forall psi 85d62bcfb82e: P2 M Ground Theory Heights  Heights KRest eq zero of forall psi 85d62bcfb82e
-- statement:
--   The P2 M Ground Theory Heights  Heights KRest eq zero of forall psi 85d62bcfb82e construction uses the P2 M Ground Theory Heights  Heights KRest eq zero of forall psi 85d62bcfb82e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L111-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L111-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic
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
open GroundTheory.Heights₂.Heights.KRest
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_KRest_eq_zero_of_forall_psi_85d62bcfb82e {t : ℝ} (h : ∀ ψ : ℝ →ₗ[ℚ] ℚ, ψ t = 0) : t = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KRest».«eq_zero_of_forall_psi» := P2M_GroundTheory_Heights__Heights_KRest_eq_zero_of_forall_psi_85d62bcfb82e
