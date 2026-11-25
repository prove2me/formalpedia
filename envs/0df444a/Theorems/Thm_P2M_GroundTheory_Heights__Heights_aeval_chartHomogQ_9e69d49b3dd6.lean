-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_chartHomogQ_9e69d49b3dd6
-- name    : P2M_GroundTheory_Heights__Heights_aeval_chartHomogQ_9e69d49b3dd6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:38:24.059786+00:00
-- url     : https://prove2.me/theorems/d89ca86b-f427-497c-b3a3-c99219f74618
-- title:
--   P2 M Ground Theory Heights  Heights aeval chart Homog Q 9e69d49b3dd6: P2 M Ground Theory Heights  Heights aeval chart Homog Q 9e69d49b3dd6
-- statement:
--   The P2 M Ground Theory Heights  Heights aeval chart Homog Q 9e69d49b3dd6 construction uses the P2 M Ground Theory Heights  Heights aeval chart Homog Q 9e69d49b3dd6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatioLemmas.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatioLemmas.lean#L25-L29

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

theorem P2M_GroundTheory_Heights__Heights_aeval_chartHomogQ_9e69d49b3dd6 {S : Type*} [CommRing S] [Algebra ℚ S] (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) (y : Coord n → S) :
    aeval y (chartHomogQ c f) = ∑ m ∈ f.support, algebraMap ℚ S (coeff m f) *
      ∏ p : Coord n, (y p ^ m p * y ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«aeval_chartHomogQ» := P2M_GroundTheory_Heights__Heights_aeval_chartHomogQ_9e69d49b3dd6
