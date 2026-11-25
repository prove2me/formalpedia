-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinBound_prod_sqrt_eq_one_c058a3ee7a59
-- name    : P2M_GroundTheory_Heights__Heights_PSymplMinBound_prod_sqrt_eq_one_c058a3ee7a59
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:22.20675+00:00
-- url     : https://prove2.me/theorems/cb7ad215-1c32-4586-9209-143f988542a6
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Min Bound prod sqrt eq one c058a3ee7a59: P2 M Ground Theory Heights  Heights PSympl Min Bound prod sqrt eq one c058a3ee7a59
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Min Bound prod sqrt eq one c058a3ee7a59 construction uses the P2 M Ground Theory Heights  Heights PSympl Min Bound prod sqrt eq one c058a3ee7a59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinBound.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinBound.lean#L11-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinBound
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
open Matrix
open GroundTheory.Heights₂.Heights.PSymplMinBound

theorem P2M_GroundTheory_Heights__Heights_PSymplMinBound_prod_sqrt_eq_one_c058a3ee7a59 {ι : Type} [Fintype ι] (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (hprod : ∏ i, lam i = 1) : ∏ i, Real.sqrt (lam i) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplMinBound».«prod_sqrt_eq_one» := P2M_GroundTheory_Heights__Heights_PSymplMinBound_prod_sqrt_eq_one_c058a3ee7a59
