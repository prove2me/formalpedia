-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_swap_b2eefeb2a9e8
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_swap_b2eefeb2a9e8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:05.163966+00:00
-- url     : https://prove2.me/theorems/854ef1a0-807e-4799-865a-7385e9cc5ccc
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip swap b2eefeb2a9e8: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip swap b2eefeb2a9e8
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip swap b2eefeb2a9e8 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip swap b2eefeb2a9e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L37-L39

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_swap_b2eefeb2a9e8 {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (a b : ι → ℂ) :
    star b ⬝ᵥ (H *ᵥ a) = star (star a ⬝ᵥ (H *ᵥ b)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«ip_swap» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_swap_b2eefeb2a9e8
