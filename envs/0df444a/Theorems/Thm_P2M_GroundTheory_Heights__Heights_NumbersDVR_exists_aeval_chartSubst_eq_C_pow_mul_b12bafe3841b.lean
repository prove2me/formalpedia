-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_aeval_chartSubst_eq_C_pow_mul_b12bafe3841b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_aeval_chartSubst_eq_C_pow_mul_b12bafe3841b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:11:19.681402+00:00
-- url     : https://prove2.me/theorems/607f8f50-a05f-4fa3-89e5-ff16f692e157
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists aeval chart Subst eq C pow mul b12bafe3841b: P2 M Ground Theory Heights  Heights Numbers DVR exists aeval chart Subst eq C pow mul b12bafe3841b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists aeval chart Subst eq C pow mul b12bafe3841b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists aeval chart Subst eq C pow mul b12bafe3841b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalChartLength.lean#L45-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalChartLength.lean#L45-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontalMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalChartLength
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
universe u
noncomputable section
variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_aeval_chartSubst_eq_C_pow_mul_b12bafe3841b (a : J → MRing ι R) (j₀ : J) (h : Polynomial (MRing ι R)) :
    ∃ (d : ℕ) (H : MRing (extIdx ι J) R),
      aeval (chartSubst a) H = Polynomial.C (a j₀ ^ d) * h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_aeval_chartSubst_eq_C_pow_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_aeval_chartSubst_eq_C_pow_mul_b12bafe3841b
