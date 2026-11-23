-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mul_mul_905a1b79b753
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mul_mul_905a1b79b753
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:45.377051+00:00
-- url     : https://prove2.me/theorems/e08053e5-56af-4573-8358-191559b8cb54
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi left Inv mul mul 905a1b79b753: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi left Inv mul mul 905a1b79b753
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi left Inv mul mul 905a1b79b753 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi left Inv mul mul 905a1b79b753 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L57-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
open Matrix
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {H : Matrix ι ι ℂ} {B : Matrix ι κ ℂ}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mul_mul_905a1b79b753 (hG : IsUnit (Bᴴ * H * B).det) {α : Type*} (N : Matrix κ α ℂ) :
    leftInv H B * (B * N) = N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«leftInv_mul_mul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mul_mul_905a1b79b753
