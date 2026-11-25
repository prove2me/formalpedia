-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_of_hForm_1ab14222c8c7
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_of_hForm_1ab14222c8c7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:53.761501+00:00
-- url     : https://prove2.me/theorems/4222225e-338c-429a-85ff-28d7ee8c0706
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume unitary of h Form 1ab14222c8c7: P2 M Ground Theory Heights  Heights Finite Covolume unitary of h Form 1ab14222c8c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume unitary of h Form 1ab14222c8c7 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume unitary of h Form 1ab14222c8c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L71-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable (H : Matrix ι ι ℂ)
variable [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_of_hForm_1ab14222c8c7 {M : Matrix ι ι ℂ}
    (hM : ∀ u z, hForm H (M *ᵥ u) (M *ᵥ z) = hForm H u z) : Mᴴ * H * M = H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«unitary_of_hForm» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_of_hForm_1ab14222c8c7
