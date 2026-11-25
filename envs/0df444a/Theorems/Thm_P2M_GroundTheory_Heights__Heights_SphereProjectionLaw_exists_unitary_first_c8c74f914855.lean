-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_exists_unitary_first_c8c74f914855
-- name    : P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_exists_unitary_first_c8c74f914855
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:40:16.550941+00:00
-- url     : https://prove2.me/theorems/aaf4b54a-bc8a-5ddf-8e1e-d672f1fa2a58
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Projection Law exists unitary first c8c74f914855: P2 M Ground Theory Heights  Heights Sphere Projection Law exists unitary first c8c74f914855
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Projection Law exists unitary first c8c74f914855 construction uses the P2 M Ground Theory Heights  Heights Sphere Projection Law exists unitary first c8c74f914855 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L62-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L62-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereProjectionLaw
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
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereProjectionLaw
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_exists_unitary_first_c8c74f914855 {m : ℕ} (p : Fin (m + 1) → ℂ) (hp : ∑ j, ‖p j‖ ^ 2 = 1) :
    ∃ U : (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (m + 1) → ℂ),
      (∀ v, ∑ j, ‖U v j‖ ^ 2 = ∑ j, ‖v j‖ ^ 2) ∧ ∀ v, U v 0 = coordAlong p v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereProjectionLaw».«exists_unitary_first» := P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_exists_unitary_first_c8c74f914855
