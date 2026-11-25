-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_exp_cont_6ec931771609
-- name    : P2M_Formalism_BasicNotions_Examples__CD_exp_cont_6ec931771609
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:32.254019+00:00
-- url     : https://prove2.me/theorems/075b1beb-6dd2-499c-9808-7346b9c9d5e3
-- title:
--   P2 M Formalism Basic Notions Examples  CD exp cont 6ec931771609: P2 M Formalism Basic Notions Examples  CD exp cont 6ec931771609
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD exp cont 6ec931771609 construction uses the P2 M Formalism Basic Notions Examples  CD exp cont 6ec931771609 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L37-L39

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

theorem P2M_Formalism_BasicNotions_Examples__CD_exp_cont_6ec931771609 : Continuous (exp : 𝔸 → 𝔸) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«exp_cont» := P2M_Formalism_BasicNotions_Examples__CD_exp_cont_6ec931771609
