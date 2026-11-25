-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplBoxVolume_set_eq_preimage_c34e58dd3381
-- name    : P2M_GroundTheory_Heights__Heights_PSymplBoxVolume_set_eq_preimage_c34e58dd3381
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:38.042491+00:00
-- url     : https://prove2.me/theorems/76e9d7e5-af31-4850-be10-9cf053c38f73
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Box Volume set eq preimage c34e58dd3381: P2 M Ground Theory Heights  Heights PSympl Box Volume set eq preimage c34e58dd3381
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Box Volume set eq preimage c34e58dd3381 construction uses the P2 M Ground Theory Heights  Heights PSympl Box Volume set eq preimage c34e58dd3381 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplBoxVolume.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplBoxVolume.lean#L11-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplBoxVolume
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
open GroundTheory.Heights₂.Heights.PSymplBoxVolume

theorem P2M_GroundTheory_Heights__Heights_PSymplBoxVolume_set_eq_preimage_c34e58dd3381 {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} =
      (Matrix.toLin' A) ⁻¹' (Set.pi Set.univ fun i => Set.Ioo (-a i) (a i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplBoxVolume».«set_eq_preimage» := P2M_GroundTheory_Heights__Heights_PSymplBoxVolume_set_eq_preimage_c34e58dd3381
