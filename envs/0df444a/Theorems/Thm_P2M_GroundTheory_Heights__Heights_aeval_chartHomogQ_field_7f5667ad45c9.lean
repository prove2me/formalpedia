-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_chartHomogQ_field_7f5667ad45c9
-- name    : P2M_GroundTheory_Heights__Heights_aeval_chartHomogQ_field_7f5667ad45c9
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:37.098881+00:00
-- url     : https://prove2.me/theorems/04b595f3-27b3-4344-b025-e506318a2976
-- title:
--   P2 M Ground Theory Heights  Heights aeval chart Homog Q field 7f5667ad45c9: P2 M Ground Theory Heights  Heights aeval chart Homog Q field 7f5667ad45c9
-- statement:
--   The P2 M Ground Theory Heights  Heights aeval chart Homog Q field 7f5667ad45c9 construction uses the P2 M Ground Theory Heights  Heights aeval chart Homog Q field 7f5667ad45c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatioLemmas.lean#L31-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatioLemmas.lean#L31-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegreeRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatioLemmas
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_aeval_chartHomogQ_field_7f5667ad45c9 {K : Type*} [Field K] [Algebra ℚ K] (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) (y : Coord n → K) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    aeval y (chartHomogQ c f) = (∏ p : Coord n, y ⟨p.1, c p.1⟩ ^ f.totalDegree) *
      aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«aeval_chartHomogQ_field» := P2M_GroundTheory_Heights__Heights_aeval_chartHomogQ_field_7f5667ad45c9
