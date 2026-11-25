-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_hasStrictFDerivAt_productLog_156a7c321b75
-- name    : P2M_Formalism_BasicNotions_Examples__CD_hasStrictFDerivAt_productLog_156a7c321b75
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:39.754629+00:00
-- url     : https://prove2.me/theorems/329fb69d-20f8-4b89-9572-84ad7080bc58
-- title:
--   P2 M Formalism Basic Notions Examples  CD has Strict FDeriv At product Log 156a7c321b75: P2 M Formalism Basic Notions Examples  CD has Strict FDeriv At product Log 156a7c321b75
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD has Strict FDeriv At product Log 156a7c321b75 construction uses the P2 M Formalism Basic Notions Examples  CD has Strict FDeriv At product Log 156a7c321b75 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L85-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L85-L86

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

theorem P2M_Formalism_BasicNotions_Examples__CD_hasStrictFDerivAt_productLog_156a7c321b75 : HasStrictFDerivAt (F2 (𝔸 := 𝔸))
    (ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸) 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«hasStrictFDerivAt_productLog» := P2M_Formalism_BasicNotions_Examples__CD_hasStrictFDerivAt_productLog_156a7c321b75
