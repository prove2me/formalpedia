-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_monic_coeff_zero_ne_315458a1ed4a
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_monic_coeff_zero_ne_315458a1ed4a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:00.219719+00:00
-- url     : https://prove2.me/theorems/fe63be05-8d2f-43e9-b103-3736dc02e60c
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model exists monic coeff zero ne 315458a1ed4a: P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model exists mo
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model exists monic coeff zero ne 315458a1ed4a construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model exists monic coeff zero ne 315458a1ed4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiniteSeparatingModel.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiniteSeparatingModel.lean#L26-L37

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_monic_coeff_zero_ne_315458a1ed4a {P : Ideal (MvPolynomial σ ℚ)} (hP : P.IsPrime)
    (ℓ : Fin e → MvPolynomial σ ℚ) {f : MvPolynomial σ ℚ} (hf : f ∉ P)
    {p : Polynomial (MvPolynomial (Fin e) ℚ)} (hp : p.Monic) (hpf : p.eval₂ (aeval ℓ).toRingHom f ∈ P) :
    ∃ q : Polynomial (MvPolynomial (Fin e) ℚ),
      q.Monic ∧ q.eval₂ (aeval ℓ).toRingHom f ∈ P ∧ q.coeff 0 ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«FiniteSeparatingModel».«exists_monic_coeff_zero_ne» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_monic_coeff_zero_ne_315458a1ed4a
