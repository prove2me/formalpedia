-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_hsG_cont_78d108c224a1
-- name    : P2M_Formalism_BasicNotions_Examples__CD_hsG_cont_78d108c224a1
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:26:53.293632+00:00
-- url     : https://prove2.me/theorems/4378ed64-3579-5345-b153-3e658dac1c80
-- title:
--   P2 M Formalism Basic Notions Examples  CD hs G cont 78d108c224a1: P2 M Formalism Basic Notions Examples  CD hs G cont 78d108c224a1
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD hs G cont 78d108c224a1 construction uses the P2 M Formalism Basic Notions Examples  CD hs G cont 78d108c224a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L110-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L110-L114

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

theorem P2M_Formalism_BasicNotions_Examples__CD_hsG_cont_78d108c224a1 {n : ℕ} (ε : Fin n → Bool) : Continuous (hsG : UJ ε → ℝ) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«hsG_cont» := P2M_Formalism_BasicNotions_Examples__CD_hsG_cont_78d108c224a1
