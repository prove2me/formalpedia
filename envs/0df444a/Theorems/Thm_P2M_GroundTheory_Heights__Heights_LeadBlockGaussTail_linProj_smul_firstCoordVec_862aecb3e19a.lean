-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_linProj_smul_firstCoordVec_862aecb3e19a
-- name    : P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_linProj_smul_firstCoordVec_862aecb3e19a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:41.806887+00:00
-- url     : https://prove2.me/theorems/eccd2db6-5e96-4215-9595-f3f58dbb8643
-- title:
--   P2 M Ground Theory Heights  Heights Lead Block Gauss Tail lin Proj smul first Coord Vec 862aecb3e19a: P2 M Ground Theory Heights  Heights Lead Block Gauss Tail lin Proj smul first Coord Vec 862aecb3e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Lead Block Gauss Tail lin Proj smul first Coord Vec 862aecb3e19a construction uses the P2 M Ground Theory Heights  Heights Lead Block Gauss Tail lin Proj smul first Coord Vec 862aecb3e19a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L174-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L174-L184

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail
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
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail

theorem P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_linProj_smul_firstCoordVec_862aecb3e19a {m n : ℕ} (π : Fin m → Fin n → ℂ) (r : ℝ) (c0 : Fin n)
    (hc0 : (c0 : ℕ) = 0) (i : Fin m) :
    linProj π ((r : ℂ) • firstCoordVec n) i = (r : ℂ) * π i c0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LeadBlockGaussTail».«linProj_smul_firstCoordVec» := P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_linProj_smul_firstCoordVec_862aecb3e19a
