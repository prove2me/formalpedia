-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_weightedHomogeneousComponent_image_27a7ee41f296
-- name    : P2M_GroundTheory_Heights__Heights_sum_weightedHomogeneousComponent_image_27a7ee41f296
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:57:10.697785+00:00
-- url     : https://prove2.me/theorems/492c18a7-0d69-55b7-9722-6923adb595a7
-- title:
--   P2 M Ground Theory Heights  Heights sum weighted Homogeneous Component image 27a7ee41f296: P2 M Ground Theory Heights  Heights sum weighted Homogeneous Component image 27a7ee41f296
-- statement:
--   The P2 M Ground Theory Heights  Heights sum weighted Homogeneous Component image 27a7ee41f296 construction uses the P2 M Ground Theory Heights  Heights sum weighted Homogeneous Component image 27a7ee41f296 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PHomogGeneratorsExist.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PHomogGeneratorsExist.lean#L13-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PHomogGeneratorsExist
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

theorem P2M_GroundTheory_Heights__Heights_sum_weightedHomogeneousComponent_image_27a7ee41f296 (f : MvPolynomial (Coord n) ℤ) :
    ∑ m ∈ f.support.image (Finsupp.weight (coordDeg n)), weightedHomogeneousComponent (coordDeg n) m f = f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sum_weightedHomogeneousComponent_image» := P2M_GroundTheory_Heights__Heights_sum_weightedHomogeneousComponent_image_27a7ee41f296
