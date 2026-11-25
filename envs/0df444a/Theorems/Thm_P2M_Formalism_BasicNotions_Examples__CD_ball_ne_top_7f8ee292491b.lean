-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_ball_ne_top_7f8ee292491b
-- name    : P2M_Formalism_BasicNotions_Examples__CD_ball_ne_top_7f8ee292491b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:28:22.463864+00:00
-- url     : https://prove2.me/theorems/416167e5-f28b-4c42-a985-7accca04145b
-- title:
--   P2 M Formalism Basic Notions Examples  CD ball ne top 7f8ee292491b: P2 M Formalism Basic Notions Examples  CD ball ne top 7f8ee292491b
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD ball ne top 7f8ee292491b construction uses the P2 M Formalism Basic Notions Examples  CD ball ne top 7f8ee292491b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L129-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L129-L154

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Matrix Formalism.REAL Formalism.UG.P Topology
open scoped ENNReal NNReal

theorem P2M_Formalism_BasicNotions_Examples__CD_ball_ne_top_7f8ee292491b {n : ℕ} (ε : Fin n → Bool) : muG ε {a | hsG a ≤ rad n} ≠ ⊤ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«ball_ne_top» := P2M_Formalism_BasicNotions_Examples__CD_ball_ne_top_7f8ee292491b
