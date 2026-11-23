-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_smul_left_c1f6b63ea674
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_smul_left_c1f6b63ea674
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:15.053207+00:00
-- url     : https://prove2.me/theorems/856870c3-5520-4568-bcc4-ce0d5a0d4c1c
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume h Form smul left c1f6b63ea674: P2 M Ground Theory Heights  Heights Finite Covolume h Form smul left c1f6b63ea674
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume h Form smul left c1f6b63ea674 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume h Form smul left c1f6b63ea674 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L35-L37

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_smul_left_c1f6b63ea674 (c : ℂ) (u z : ι → ℂ) :
    hForm H (c • u) z = starRingEnd ℂ c * hForm H u z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«hForm_smul_left» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_smul_left_c1f6b63ea674
