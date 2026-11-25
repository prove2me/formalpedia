-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_exp_neg_mul_b0802c46782f
-- name    : P2M_Formalism_BasicNotions_Examples__CD_exp_neg_mul_b0802c46782f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:47.010552+00:00
-- url     : https://prove2.me/theorems/148d61a9-60c9-4680-aece-85f3feb2466a
-- title:
--   P2 M Formalism Basic Notions Examples  CD exp neg mul b0802c46782f: P2 M Formalism Basic Notions Examples  CD exp neg mul b0802c46782f
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD exp neg mul b0802c46782f construction uses the P2 M Formalism Basic Notions Examples  CD exp neg mul b0802c46782f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L41-L43

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

theorem P2M_Formalism_BasicNotions_Examples__CD_exp_neg_mul_b0802c46782f (X : 𝔸) : exp (-X) * exp X = 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«exp_neg_mul» := P2M_Formalism_BasicNotions_Examples__CD_exp_neg_mul_b0802c46782f
