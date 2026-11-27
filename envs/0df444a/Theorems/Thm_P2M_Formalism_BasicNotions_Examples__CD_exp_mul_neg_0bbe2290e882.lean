-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_exp_mul_neg_0bbe2290e882
-- name    : P2M_Formalism_BasicNotions_Examples__CD_exp_mul_neg_0bbe2290e882
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:13.07933+00:00
-- url     : https://prove2.me/theorems/3385ddeb-9424-5ee9-a384-91e6a4fb48a5
-- title:
--   P2 M Formalism Basic Notions Examples  CD exp mul neg 0bbe2290e882: P2 M Formalism Basic Notions Examples  CD exp mul neg 0bbe2290e882
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD exp mul neg 0bbe2290e882 construction uses the P2 M Formalism Basic Notions Examples  CD exp mul neg 0bbe2290e882 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L45-L47

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

theorem P2M_Formalism_BasicNotions_Examples__CD_exp_mul_neg_0bbe2290e882 (X : 𝔸) : exp X * exp (-X) = 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«exp_mul_neg» := P2M_Formalism_BasicNotions_Examples__CD_exp_mul_neg_0bbe2290e882
