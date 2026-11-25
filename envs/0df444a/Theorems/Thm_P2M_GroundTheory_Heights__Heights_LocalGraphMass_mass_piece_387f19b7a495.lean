-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_mass_piece_387f19b7a495
-- name    : P2M_GroundTheory_Heights__Heights_LocalGraphMass_mass_piece_387f19b7a495
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:32.805891+00:00
-- url     : https://prove2.me/theorems/dcf3776d-804d-41e7-ace6-4bf6b42e0f69
-- title:
--   P2 M Ground Theory Heights  Heights Local Graph Mass mass piece 387f19b7a495: P2 M Ground Theory Heights  Heights Local Graph Mass mass piece 387f19b7a495
-- statement:
--   The P2 M Ground Theory Heights  Heights Local Graph Mass mass piece 387f19b7a495 construction uses the P2 M Ground Theory Heights  Heights Local Graph Mass mass piece 387f19b7a495 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphMass.lean#L91-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphMass.lean#L91-L107

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass
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
open GroundTheory.Heights₂.Heights.LocalGraphMass
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LocalGraphMass_mass_piece_387f19b7a495 (hPF : ProjectionFormula.Statement)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n)) {d : ℕ}
    (hd : I₀.card = d) (Ω : Set (I₀ → ℂ)) (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n))
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (hfix : ∀ w ∈ Ω, frameProj b I₀ (g w) = w)
    (M : Set (EuclideanSpace ℂ (Fin n))) (hM : MeasurableSet M) :
    μH[((2 * d : ℕ) : ℝ)] (g '' Ω ∩ M) =
      ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
        frameFibreCount b I (g '' Ω ∩ M) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocalGraphMass».«mass_piece» := P2M_GroundTheory_Heights__Heights_LocalGraphMass_mass_piece_387f19b7a495
