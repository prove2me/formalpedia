-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_heisS_036f0895ef05
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_heisS_036f0895ef05
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:56.607113+00:00
-- url     : https://prove2.me/theorems/82480b54-bbd4-4197-9082-a596ef38aca3
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume eq heis S 036f0895ef05: P2 M Ground Theory Heights  Heights Finite Covolume eq heis S 036f0895ef05
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume eq heis S 036f0895ef05 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume eq heis S 036f0895ef05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L114-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L114-L121

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
variable {H : Matrix ι ι ℂ}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_heisS_036f0895ef05 {y : ι → ℂ} {s : ℂ} (hs : s + starRingEnd ℂ s + hForm H y y = 0) :
    s = heisS H y s.im := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«eq_heisS» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_heisS_036f0895ef05
