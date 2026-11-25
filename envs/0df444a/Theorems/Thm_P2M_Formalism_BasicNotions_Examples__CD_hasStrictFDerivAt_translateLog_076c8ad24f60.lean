-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_hasStrictFDerivAt_translateLog_076c8ad24f60
-- name    : P2M_Formalism_BasicNotions_Examples__CD_hasStrictFDerivAt_translateLog_076c8ad24f60
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:45.453804+00:00
-- url     : https://prove2.me/theorems/48f457ad-9f65-49fb-9875-4790e7536b31
-- title:
--   P2 M Formalism Basic Notions Examples  CD has Strict FDeriv At translate Log 076c8ad24f60: P2 M Formalism Basic Notions Examples  CD has Strict FDeriv At translate Log 076c8ad24f60
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD has Strict FDeriv At translate Log 076c8ad24f60 construction uses the P2 M Formalism Basic Notions Examples  CD has Strict FDeriv At translate Log 076c8ad24f60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L74-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L74-L83

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
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
open Filter Topology Metric NormedSpace Asymptotics
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem P2M_Formalism_BasicNotions_Examples__CD_hasStrictFDerivAt_translateLog_076c8ad24f60 : HasStrictFDerivAt (F1 (𝔸 := 𝔸)) (ContinuousLinearMap.snd ℝ 𝔸 𝔸) 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«hasStrictFDerivAt_translateLog» := P2M_Formalism_BasicNotions_Examples__CD_hasStrictFDerivAt_translateLog_076c8ad24f60
