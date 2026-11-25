-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_mass_piece_frame_d4356ba17c2f
-- name    : P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_mass_piece_frame_d4356ba17c2f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:16.445108+00:00
-- url     : https://prove2.me/theorems/fc8f52b4-9641-4e79-abb8-e727a55b4d11
-- title:
--   P2 M Ground Theory Heights  Heights Local Graph Projection Mass mass piece frame d4356ba17c2f: P2 M Ground Theory Heights  Heights Local Graph Projection Mass mass piece frame d4356ba17c2f
-- statement:
--   The P2 M Ground Theory Heights  Heights Local Graph Projection Mass mass piece frame d4356ba17c2f construction uses the P2 M Ground Theory Heights  Heights Local Graph Projection Mass mass piece frame d4356ba17c2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphProjectionMass.lean#L37-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphProjectionMass.lean#L37-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphProjectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphProjectionMass
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
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LocalGraphProjectionMass
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_mass_piece_frame_d4356ba17c2f (hPF : ProjectionFormula.Statement)
    (b c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n)) {d : ℕ}
    (hd : I₀.card = d) (Ω : Set (I₀ → ℂ)) (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n))
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (hfix : ∀ w ∈ Ω, frameProj b I₀ (g w) = w)
    (M : Set (EuclideanSpace ℂ (Fin n))) (hM : MeasurableSet M) :
    μH[((2 * d : ℕ) : ℝ)] (g '' Ω ∩ M) =
      ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
        frameFibreCount c I (g '' Ω ∩ M) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocalGraphProjectionMass».«mass_piece_frame» := P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_mass_piece_frame_d4356ba17c2f
