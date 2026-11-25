-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplShortPrim_intVec_smul_63230d9938e4
-- name    : P2M_GroundTheory_Heights__Heights_PSymplShortPrim_intVec_smul_63230d9938e4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:14:04.722556+00:00
-- url     : https://prove2.me/theorems/abf6d41f-5816-5789-b573-ff9db8b3265a
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Short Prim int Vec smul 63230d9938e4: P2 M Ground Theory Heights  Heights PSympl Short Prim int Vec smul 63230d9938e4
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Short Prim int Vec smul 63230d9938e4 construction uses the P2 M Ground Theory Heights  Heights PSympl Short Prim int Vec smul 63230d9938e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplShortPrim.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplShortPrim.lean#L11-L13

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

theorem P2M_GroundTheory_Heights__Heights_PSymplShortPrim_intVec_smul_63230d9938e4 {ι : Type} (m : ℤ) (w : ι → ℤ) : intVec (m • w) = (m : ℝ) • intVec w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplShortPrim».«intVec_smul» := P2M_GroundTheory_Heights__Heights_PSymplShortPrim_intVec_smul_63230d9938e4
