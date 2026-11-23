-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_sesq_mul_064c0e5bfacf
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_sesq_mul_064c0e5bfacf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:04.586967+00:00
-- url     : https://prove2.me/theorems/9c30a34a-c0bc-4e68-ac79-016df6cb39ed
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi sesq mul 064c0e5bfacf: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi sesq mul 064c0e5bfacf
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi sesq mul 064c0e5bfacf construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi sesq mul 064c0e5bfacf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L25-L27

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_sesq_mul_064c0e5bfacf (H : Matrix ι ι ℂ) (M : Matrix ι κ ℂ) (N : Matrix ι κ' ℂ) (c : κ → ℂ)
    (d : κ' → ℂ) : star c ⬝ᵥ ((Mᴴ * H * N) *ᵥ d) = star (M *ᵥ c) ⬝ᵥ (H *ᵥ (N *ᵥ d)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«sesq_mul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_sesq_mul_064c0e5bfacf
