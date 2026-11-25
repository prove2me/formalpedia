-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ext_sesq_f168d8060b14
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ext_sesq_f168d8060b14
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:28.498239+00:00
-- url     : https://prove2.me/theorems/18909fc8-96c5-4f23-be92-d3013cabdf7f
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ext sesq f168d8060b14: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ext sesq f168d8060b14
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ext sesq f168d8060b14 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ext sesq f168d8060b14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L29-L35

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
variable {κ' : Type*} [Fintype κ']

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ext_sesq_f168d8060b14 {M N : Matrix κ κ ℂ}
    (h : ∀ c d : κ → ℂ, star c ⬝ᵥ (M *ᵥ d) = star c ⬝ᵥ (N *ᵥ d)) : M = N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«ext_sesq» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ext_sesq_f168d8060b14
