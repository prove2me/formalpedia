-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_pos_c2277533c6b6
-- name    : P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_pos_c2277533c6b6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:27:12.536316+00:00
-- url     : https://prove2.me/theorems/03300214-282d-50ec-a2e2-50b650a05970
-- title:
--   P2 M Formalism Basic Notions Examples  CD cd Scale Of pos c2277533c6b6: P2 M Formalism Basic Notions Examples  CD cd Scale Of pos c2277533c6b6
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD cd Scale Of pos c2277533c6b6 construction uses the P2 M Formalism Basic Notions Examples  CD cd Scale Of pos c2277533c6b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L237-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L237-L238

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
variable (C : CDHaar)

theorem P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_pos_c2277533c6b6 (n : ℕ) (ε : Fin n → Bool) : 0 < cdScaleOf C n ε := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«cdScaleOf_pos» := P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_pos_c2277533c6b6
