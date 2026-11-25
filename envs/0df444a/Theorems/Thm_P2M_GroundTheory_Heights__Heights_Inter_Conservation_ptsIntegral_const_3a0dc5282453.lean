-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_ptsIntegral_const_3a0dc5282453
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Conservation_ptsIntegral_const_3a0dc5282453
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:28.345902+00:00
-- url     : https://prove2.me/theorems/47fcf854-944b-4d9a-a69f-0f2eb2b93294
-- title:
--   P2 M Ground Theory Heights  Heights Inter Conservation pts Integral const 3a0dc5282453: P2 M Ground Theory Heights  Heights Inter Conservation pts Integral const 3a0dc5282453
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Conservation pts Integral const 3a0dc5282453 construction uses the P2 M Ground Theory Heights  Heights Inter Conservation pts Integral const 3a0dc5282453 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ConservationDegreeFormOfExistence.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ConservationDegreeFormOfExistence.lean#L18-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.Inter.Conservation
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_Conservation_ptsIntegral_const_3a0dc5282453 {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Conservation».«ptsIntegral_const» := P2M_GroundTheory_Heights__Heights_Inter_Conservation_ptsIntegral_const_3a0dc5282453
