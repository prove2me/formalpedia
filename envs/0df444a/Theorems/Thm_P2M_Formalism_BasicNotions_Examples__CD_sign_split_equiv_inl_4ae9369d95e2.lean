-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_sign_split_equiv_inl_4ae9369d95e2
-- name    : P2M_Formalism_BasicNotions_Examples__CD_sign_split_equiv_inl_4ae9369d95e2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:27:27.411591+00:00
-- url     : https://prove2.me/theorems/17211496-b9b3-5c22-8e90-97f1f83645a8
-- title:
--   P2 M Formalism Basic Notions Examples  CD sign split equiv inl 4ae9369d95e2: P2 M Formalism Basic Notions Examples  CD sign split equiv inl 4ae9369d95e2
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD sign split equiv inl 4ae9369d95e2 construction uses the P2 M Formalism Basic Notions Examples  CD sign split equiv inl 4ae9369d95e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L197-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L197-L199

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

theorem P2M_Formalism_BasicNotions_Examples__CD_sign_split_equiv_inl_4ae9369d95e2 {n : ℕ} (ε : Fin n → Bool) (i) : ε (e0 ε (Sum.inl i)) = true := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«sign_split_equiv_inl» := P2M_Formalism_BasicNotions_Examples__CD_sign_split_equiv_inl_4ae9369d95e2
