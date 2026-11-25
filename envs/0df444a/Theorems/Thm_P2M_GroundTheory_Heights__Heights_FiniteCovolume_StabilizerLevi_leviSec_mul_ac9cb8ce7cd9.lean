-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_mul_ac9cb8ce7cd9
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_mul_ac9cb8ce7cd9
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:45.315857+00:00
-- url     : https://prove2.me/theorems/79376133-9c66-407b-a1a9-b27d5ad9262c
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Sec mul ac9cb8ce7cd9: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Sec mul ac9cb8ce7cd9
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Sec mul ac9cb8ce7cd9 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi levi Sec mul ac9cb8ce7cd9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L69-L74

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_mul_ac9cb8ce7cd9 (hG : IsUnit (Bᴴ * H * B).det) (m m' : Matrix κ κ ℂ) :
    leviSec H B (m * m') = leviSec H B m * leviSec H B m' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«leviSec_mul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_mul_ac9cb8ce7cd9
