-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_of_unitary_4c2fa1afaeb5
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_of_unitary_4c2fa1afaeb5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:21:45.595047+00:00
-- url     : https://prove2.me/theorems/044568d0-80ac-47c8-841d-4ad59aee624e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume h Form mul Vec of unitary 4c2fa1afaeb5: P2 M Ground Theory Heights  Heights Finite Covolume h Form mul Vec of unitary 4c2fa1afaeb5
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume h Form mul Vec of unitary 4c2fa1afaeb5 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume h Form mul Vec of unitary 4c2fa1afaeb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L61-L63

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_of_unitary_4c2fa1afaeb5 {M : Matrix ι ι ℂ} (hM : Mᴴ * H * M = H) (u z : ι → ℂ) :
    hForm H (M *ᵥ u) (M *ᵥ z) = hForm H u z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«hForm_mulVec_of_unitary» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_of_unitary_4c2fa1afaeb5
