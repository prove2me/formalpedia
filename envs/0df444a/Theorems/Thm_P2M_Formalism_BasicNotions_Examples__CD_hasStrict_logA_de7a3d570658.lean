-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_hasStrict_logA_de7a3d570658
-- name    : P2M_Formalism_BasicNotions_Examples__CD_hasStrict_logA_de7a3d570658
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:36.914224+00:00
-- url     : https://prove2.me/theorems/9dbfaa7f-0f14-4f76-9f9c-d3804453edbc
-- title:
--   P2 M Formalism Basic Notions Examples  CD has Strict log A de7a3d570658: P2 M Formalism Basic Notions Examples  CD has Strict log A de7a3d570658
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD has Strict log A de7a3d570658 construction uses the P2 M Formalism Basic Notions Examples  CD has Strict log A de7a3d570658 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L32-L35

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

theorem P2M_Formalism_BasicNotions_Examples__CD_hasStrict_logA_de7a3d570658 : HasStrictFDerivAt (logA 𝔸) (ContinuousLinearMap.id ℝ 𝔸) (1 : 𝔸) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«hasStrict_logA» := P2M_Formalism_BasicNotions_Examples__CD_hasStrict_logA_de7a3d570658
