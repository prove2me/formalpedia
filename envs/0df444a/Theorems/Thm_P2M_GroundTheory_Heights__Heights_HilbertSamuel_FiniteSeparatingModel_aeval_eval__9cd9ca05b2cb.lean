-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_aeval_eval__9cd9ca05b2cb
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_aeval_eval__9cd9ca05b2cb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:31.168176+00:00
-- url     : https://prove2.me/theorems/ee531729-a22c-5e83-b2b9-fda047823dd3
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model aeval eval  9cd9ca05b2cb: P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model aeval eval  9cd9ca05b2cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model aeval eval  9cd9ca05b2cb construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model aeval eval  9cd9ca05b2cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiniteSeparatingModel.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiniteSeparatingModel.lean#L15-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiniteSeparatingModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsNoetherProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsLiftToZeros
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiniteSeparatingModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel
variable {σ : Type} {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_aeval_eval__9cd9ca05b2cb (ℓ : Fin e → MvPolynomial σ ℚ) (Q : Polynomial (MvPolynomial (Fin e) ℚ))
    (g : MvPolynomial σ ℚ) (z : σ → ℂ) :
    aeval z (Q.eval₂ (aeval ℓ).toRingHom g) =
      Q.eval₂ (aeval fun j => aeval z (ℓ j)).toRingHom (aeval z g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«FiniteSeparatingModel».«aeval_eval₂» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_aeval_eval__9cd9ca05b2cb
