-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sigma_mem_points_5c3b047266ee
-- name    : P2M_GroundTheory_Heights__Heights_sigma_mem_points_5c3b047266ee
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:58.581985+00:00
-- url     : https://prove2.me/theorems/ef71f735-55d6-40b0-9804-babf7b49992b
-- title:
--   P2 M Ground Theory Heights  Heights sigma mem points 5c3b047266ee: P2 M Ground Theory Heights  Heights sigma mem points 5c3b047266ee
-- statement:
--   The P2 M Ground Theory Heights  Heights sigma mem points 5c3b047266ee construction uses the P2 M Ground Theory Heights  Heights sigma mem points 5c3b047266ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FiniteSupportHeight.lean#L19-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FiniteSupportHeight.lean#L19-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_sigma_mem_points_5c3b047266ee {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (P : ArithVariety n)
    {x : Cone n (AlgebraicClosure ℚ)} (hx : x ∈ P.points (AlgebraicClosure ℚ))
    (σ : coordField x →+* ℂ) : (fun k i ↦ σ (coordVec x k i)) ∈ P.points ℂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sigma_mem_points» := P2M_GroundTheory_Heights__Heights_sigma_mem_points_5c3b047266ee
