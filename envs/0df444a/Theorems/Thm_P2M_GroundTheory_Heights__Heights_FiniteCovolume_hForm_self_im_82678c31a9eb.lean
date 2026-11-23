-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_self_im_82678c31a9eb
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_self_im_82678c31a9eb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:50.922646+00:00
-- url     : https://prove2.me/theorems/5495af31-ec91-4e71-84fa-cc019be3e42f
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume h Form self im 82678c31a9eb: P2 M Ground Theory Heights  Heights Finite Covolume h Form self im 82678c31a9eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume h Form self im 82678c31a9eb construction uses the P2 M Ground Theory Heights  Heights Finite Covolume h Form self im 82678c31a9eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L52-L54

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_self_im_82678c31a9eb {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (u : ι → ℂ) :
    (hForm H u u).im = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«hForm_self_im» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_self_im_82678c31a9eb
