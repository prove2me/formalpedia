-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_mulVec_of_8771abea5030
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_mulVec_of_8771abea5030
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:21.873928+00:00
-- url     : https://prove2.me/theorems/61660fc1-4977-4c7b-8561-e19df2d1db4c
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Sec mul Vec of 8771abea5030: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Sec mul Vec of 8771abea50
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Sec mul Vec of 8771abea5030 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Sec mul Vec of 8771abea5030 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L87-L91

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_mulVec_of_8771abea5030 {X : ι → ℂ} (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0) (m : Matrix κ κ ℂ) :
    leviSec H B m *ᵥ X = X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«leviSec_mulVec_of» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_mulVec_of_8771abea5030
