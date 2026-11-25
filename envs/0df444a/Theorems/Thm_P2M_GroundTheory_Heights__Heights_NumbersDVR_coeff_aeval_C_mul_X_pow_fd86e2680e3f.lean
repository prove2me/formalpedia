-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_coeff_aeval_C_mul_X_pow_fd86e2680e3f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_coeff_aeval_C_mul_X_pow_fd86e2680e3f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:12:26.446869+00:00
-- url     : https://prove2.me/theorems/eb216b00-4901-438b-a9ba-fc33dfc164f1
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR coeff aeval C mul X pow fd86e2680e3f: P2 M Ground Theory Heights  Heights Numbers DVR coeff aeval C mul X pow fd86e2680e3f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR coeff aeval C mul X pow fd86e2680e3f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR coeff aeval C mul X pow fd86e2680e3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpModel.lean#L34-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpModel.lean#L34-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpModel
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
variable {σ : Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_coeff_aeval_C_mul_X_pow_fd86e2680e3f {B : Type*} [CommRing B] [Algebra R B] (a : σ → B) (ω : σ → ℕ)
    (n : ℕ) (p : MvPolynomial σ R) :
    (aeval (fun v => Polynomial.C (a v) * Polynomial.X ^ ω v) p).coeff n =
      aeval a (weightedHomogeneousComponent ω n p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«coeff_aeval_C_mul_X_pow» := P2M_GroundTheory_Heights__Heights_NumbersDVR_coeff_aeval_C_mul_X_pow_fd86e2680e3f
