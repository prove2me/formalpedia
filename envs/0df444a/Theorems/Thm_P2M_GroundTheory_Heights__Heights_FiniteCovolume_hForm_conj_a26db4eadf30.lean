-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:21.433436+00:00
-- url     : https://prove2.me/theorems/cec0884f-aab7-4d07-b5e5-e0a370523ab6
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume h Form conj a26db4eadf30: P2 M Ground Theory Heights  Heights Finite Covolume h Form conj a26db4eadf30
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume h Form conj a26db4eadf30 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume h Form conj a26db4eadf30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L46-L50

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30 {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (u z : ι → ℂ) :
    starRingEnd ℂ (hForm H u z) = hForm H z u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«hForm_conj» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30
