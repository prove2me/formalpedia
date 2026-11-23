-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_debb3da7c3fb
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_debb3da7c3fb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:20.289674+00:00
-- url     : https://prove2.me/theorems/fa14cac1-670c-49a9-abdf-620fb620eb28
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Mat mul Vec debb3da7c3fb: P2 M Ground Theory Heights  Heights Finite Covolume heis Mat mul Vec debb3da7c3fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Mat mul Vec debb3da7c3fb construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Mat mul Vec debb3da7c3fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L134-L136

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
variable [DecidableEq ι]
variable {H : Matrix ι ι ℂ} {a : ι → ℂ}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_debb3da7c3fb (y : ι → ℂ) (s : ℂ) (z : ι → ℂ) :
    heisMat H a y s *ᵥ z = z + hForm H a z • (y + s • a) - hForm H y z • a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisMat_mulVec» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_debb3da7c3fb
