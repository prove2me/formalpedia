-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_vectorL2Norm_conj_a383f706a1f4
-- name    : P2M_GroundTheory_Heights__Heights_vectorL2Norm_conj_a383f706a1f4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:47.919947+00:00
-- url     : https://prove2.me/theorems/81708b73-c528-45ba-a68f-2a3e8362a34b
-- title:
--   P2 M Ground Theory Heights  Heights vector L2 Norm conj a383f706a1f4: P2 M Ground Theory Heights  Heights vector L2 Norm conj a383f706a1f4
-- statement:
--   The P2 M Ground Theory Heights  Heights vector L2 Norm conj a383f706a1f4 construction uses the P2 M Ground Theory Heights  Heights vector L2 Norm conj a383f706a1f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Points.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Points.lean#L99-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
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
open MvPolynomial NumberField
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_vectorL2Norm_conj_a383f706a1f4 {m : ℕ} (w : Fin m → ℂ) :
    l2Norm (fun i ↦ starRingEnd ℂ (w i)) = l2Norm w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«vectorL2Norm_conj» := P2M_GroundTheory_Heights__Heights_vectorL2Norm_conj_a383f706a1f4
