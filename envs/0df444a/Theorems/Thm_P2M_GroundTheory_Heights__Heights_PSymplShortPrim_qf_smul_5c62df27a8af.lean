-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplShortPrim_qf_smul_5c62df27a8af
-- name    : P2M_GroundTheory_Heights__Heights_PSymplShortPrim_qf_smul_5c62df27a8af
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:27.055808+00:00
-- url     : https://prove2.me/theorems/4aab4ad9-3fcc-421c-a272-8c828cbf9f2d
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Short Prim qf smul 5c62df27a8af: P2 M Ground Theory Heights  Heights PSympl Short Prim qf smul 5c62df27a8af
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Short Prim qf smul 5c62df27a8af construction uses the P2 M Ground Theory Heights  Heights PSympl Short Prim qf smul 5c62df27a8af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplShortPrim.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplShortPrim.lean#L15-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplShortPrim
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
open GroundTheory.Heights₂.Heights.PSymplShortPrim

theorem P2M_GroundTheory_Heights__Heights_PSymplShortPrim_qf_smul_5c62df27a8af {ι : Type} [Fintype ι] (Y : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) :
    qf Y (c • x) = c ^ 2 * qf Y x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplShortPrim».«qf_smul» := P2M_GroundTheory_Heights__Heights_PSymplShortPrim_qf_smul_5c62df27a8af
