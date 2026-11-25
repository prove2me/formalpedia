-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionInjectivity_isLive_of_mem_points_9bcc7614fe08
-- name    : P2M_GroundTheory_Heights__Heights_SectionInjectivity_isLive_of_mem_points_9bcc7614fe08
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:32.325413+00:00
-- url     : https://prove2.me/theorems/0c2951e4-a1c6-4406-9c36-40a753f427ff
-- title:
--   P2 M Ground Theory Heights  Heights Section Injectivity is Live of mem points 9bcc7614fe08: P2 M Ground Theory Heights  Heights Section Injectivity is Live of mem points 9bcc7614fe08
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Injectivity is Live of mem points 9bcc7614fe08 construction uses the P2 M Ground Theory Heights  Heights Section Injectivity is Live of mem points 9bcc7614fe08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroMore.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroMore.lean#L17-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroMore
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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionInjectivity
set_option linter.unusedSectionVars false

theorem P2M_GroundTheory_Heights__Heights_SectionInjectivity_isLive_of_mem_points_9bcc7614fe08 {P : ArithVariety n} {z : Cone n ℂ} (hz : z ∈ P.points ℂ)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, z k (c k) ≠ 0) :
    ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionInjectivity».«isLive_of_mem_points» := P2M_GroundTheory_Heights__Heights_SectionInjectivity_isLive_of_mem_points_9bcc7614fe08
