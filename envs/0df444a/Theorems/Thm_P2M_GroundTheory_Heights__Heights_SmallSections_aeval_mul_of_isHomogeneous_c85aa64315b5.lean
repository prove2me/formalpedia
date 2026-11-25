-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_aeval_mul_of_isHomogeneous_c85aa64315b5
-- name    : P2M_GroundTheory_Heights__Heights_SmallSections_aeval_mul_of_isHomogeneous_c85aa64315b5
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:05.816382+00:00
-- url     : https://prove2.me/theorems/341daa0f-1d38-4b3a-9afe-779c4b241d74
-- title:
--   P2 M Ground Theory Heights  Heights Small Sections aeval mul of is Homogeneous c85aa64315b5: P2 M Ground Theory Heights  Heights Small Sections aeval mul of is Homogeneous c85aa64315b5
-- statement:
--   The P2 M Ground Theory Heights  Heights Small Sections aeval mul of is Homogeneous c85aa64315b5 construction uses the P2 M Ground Theory Heights  Heights Small Sections aeval mul of is Homogeneous c85aa64315b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L15-L28

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

theorem P2M_GroundTheory_Heights__Heights_SmallSections_aeval_mul_of_isHomogeneous_c85aa64315b5 {σ A : Type*} [CommRing A] [Algebra ℤ A] {F : MvPolynomial σ ℤ} {τ : ℕ}
    (hF : F.IsHomogeneous τ) (t : A) (x : σ → A) :
    aeval (fun j ↦ t * x j) F = t ^ τ * aeval x F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SmallSections».«aeval_mul_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_SmallSections_aeval_mul_of_isHomogeneous_c85aa64315b5
