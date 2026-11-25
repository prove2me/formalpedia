-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_minpoly_426ccccab7a9
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_minpoly_426ccccab7a9
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:45.114324+00:00
-- url     : https://prove2.me/theorems/45cf1ff0-0715-4ba8-aacb-c0b8487673d3
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model exists minpoly 426ccccab7a9: P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model exists minpoly 426ccc
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model exists minpoly 426ccccab7a9 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model exists minpoly 426ccccab7a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiniteSeparatingModel.lean#L41-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiniteSeparatingModel.lean#L41-L65

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
set_option synthInstance.maxHeartbeats 400000

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_minpoly_426ccccab7a9 {P : Ideal (MvPolynomial σ ℚ)} (hP : P.IsPrime)
    (ℓ : Fin e → MvPolynomial σ ℚ) (hinj : ∀ q : MvPolynomial (Fin e) ℚ, aeval ℓ q ∈ P → q = 0)
    (hint : ∀ g : MvPolynomial σ ℚ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ),
      p.Monic ∧ p.eval₂ (aeval ℓ).toRingHom g ∈ P) (u : MvPolynomial σ ℚ) :
    ∃ G : Polynomial (MvPolynomial (Fin e) ℚ), G.Monic ∧ G.eval₂ (aeval ℓ).toRingHom u ∈ P ∧
      ∀ Q : Polynomial (MvPolynomial (Fin e) ℚ), Q.eval₂ (aeval ℓ).toRingHom u ∈ P → G ∣ Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«FiniteSeparatingModel».«exists_minpoly» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_minpoly_426ccccab7a9
