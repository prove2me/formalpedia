-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviProj_leviSec_434dd2fc110f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviProj_leviSec_434dd2fc110f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:26.36681+00:00
-- url     : https://prove2.me/theorems/b8f8fd3f-8ccb-4ebc-bb9b-68f3551c84c0
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Proj levi Sec 434dd2fc110f: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Proj levi Sec 434dd2fc110f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Proj levi Sec 434dd2fc110f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Proj levi Sec 434dd2fc110f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L79-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L79-L85

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviProj_leviSec_434dd2fc110f (hG : IsUnit (Bᴴ * H * B).det) (m : Matrix κ κ ℂ) :
    leviProj H B (leviSec H B m) = m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«leviProj_leviSec» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviProj_leviSec_434dd2fc110f
