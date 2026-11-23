-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_462e477e9506
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_462e477e9506
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:57.818931+00:00
-- url     : https://prove2.me/theorems/345437c0-a696-40f6-861e-fa8609d30067
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume h Form mul Vec 462e477e9506: P2 M Ground Theory Heights  Heights Finite Covolume h Form mul Vec 462e477e9506
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume h Form mul Vec 462e477e9506 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume h Form mul Vec 462e477e9506 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L56-L59

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_462e477e9506 (M : Matrix ι ι ℂ) (u z : ι → ℂ) :
    hForm H (M *ᵥ u) (M *ᵥ z) = hForm (Mᴴ * H * M) u z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«hForm_mulVec» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_462e477e9506
