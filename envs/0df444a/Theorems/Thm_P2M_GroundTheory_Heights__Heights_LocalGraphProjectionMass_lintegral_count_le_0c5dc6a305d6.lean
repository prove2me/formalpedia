-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_lintegral_count_le_0c5dc6a305d6
-- name    : P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_lintegral_count_le_0c5dc6a305d6
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:55.693578+00:00
-- url     : https://prove2.me/theorems/bdedd584-9fd6-4ca4-a1f1-58b5118e5257
-- title:
--   P2 M Ground Theory Heights  Heights Local Graph Projection Mass lintegral count le 0c5dc6a305d6: P2 M Ground Theory Heights  Heights Local Graph Projection Mass lintegral count le 0c5dc6a305d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Local Graph Projection Mass lintegral count le 0c5dc6a305d6 construction uses the P2 M Ground Theory Heights  Heights Local Graph Projection Mass lintegral count le 0c5dc6a305d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphProjectionMass.lean#L55-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphProjectionMass.lean#L55-L110

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

theorem P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_lintegral_count_le_0c5dc6a305d6 (U : Matrix (Fin n) (Fin n) ℂ)
    (c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hc : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (c i) z = ∑ j, U i j * z j)
    {d : ℕ} (I : Finset (Fin n)) (hI : I.card = d) (A : Set (EuclideanSpace ℂ (Fin n))) :
    ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount c I A (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) ≤
      (⨆ y : EuclideanSpace ℂ (Fin d),
          (({z | z ∈ A ∧ rowsProj U (I.orderEmbOfFin hI) z = y}.encard : ℕ∞) : ℝ≥0∞)) *
        μH[((2 * d : ℕ) : ℝ)] (rowsProj U (I.orderEmbOfFin hI) '' A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocalGraphProjectionMass».«lintegral_count_le» := P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_lintegral_count_le_0c5dc6a305d6
