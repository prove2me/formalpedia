-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_isWeightedHomogeneous_aeval_85f3de089ad9
-- name    : P2M_GroundTheory_Heights__Heights_SmallSections_isWeightedHomogeneous_aeval_85f3de089ad9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:08.655376+00:00
-- url     : https://prove2.me/theorems/67afcf8e-1544-4421-a4de-9b4020bcdab7
-- title:
--   P2 M Ground Theory Heights  Heights Small Sections is Weighted Homogeneous aeval 85f3de089ad9: P2 M Ground Theory Heights  Heights Small Sections is Weighted Homogeneous aeval 85f3de089ad9
-- statement:
--   The P2 M Ground Theory Heights  Heights Small Sections is Weighted Homogeneous aeval 85f3de089ad9 construction uses the P2 M Ground Theory Heights  Heights Small Sections is Weighted Homogeneous aeval 85f3de089ad9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L32-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
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
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_SmallSections_isWeightedHomogeneous_aeval_85f3de089ad9 {σ : Type*} {F : MvPolynomial σ ℤ} {τ : ℕ} (hF : F.IsHomogeneous τ)
    {g : σ → MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hg : ∀ j, IsWeightedHomogeneous (coordDeg n) (g j) δ) :
    IsWeightedHomogeneous (coordDeg n) (aeval g F) (τ • δ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SmallSections».«isWeightedHomogeneous_aeval» := P2M_GroundTheory_Heights__Heights_SmallSections_isWeightedHomogeneous_aeval_85f3de089ad9
