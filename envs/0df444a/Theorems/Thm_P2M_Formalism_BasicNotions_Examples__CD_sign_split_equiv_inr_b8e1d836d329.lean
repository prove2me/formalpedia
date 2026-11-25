-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_sign_split_equiv_inr_b8e1d836d329
-- name    : P2M_Formalism_BasicNotions_Examples__CD_sign_split_equiv_inr_b8e1d836d329
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:27:31.176166+00:00
-- url     : https://prove2.me/theorems/82782600-f197-4da5-983d-851598441cf2
-- title:
--   P2 M Formalism Basic Notions Examples  CD sign split equiv inr b8e1d836d329: P2 M Formalism Basic Notions Examples  CD sign split equiv inr b8e1d836d329
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD sign split equiv inr b8e1d836d329 construction uses the P2 M Formalism Basic Notions Examples  CD sign split equiv inr b8e1d836d329 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L201-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L201-L203

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

theorem P2M_Formalism_BasicNotions_Examples__CD_sign_split_equiv_inr_b8e1d836d329 {n : ℕ} (ε : Fin n → Bool) (j) : ε (e0 ε (Sum.inr j)) = false := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«sign_split_equiv_inr» := P2M_Formalism_BasicNotions_Examples__CD_sign_split_equiv_inr_b8e1d836d329
