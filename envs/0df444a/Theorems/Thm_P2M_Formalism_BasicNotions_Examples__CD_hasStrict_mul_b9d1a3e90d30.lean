-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_hasStrict_mul_b9d1a3e90d30
-- name    : P2M_Formalism_BasicNotions_Examples__CD_hasStrict_mul_b9d1a3e90d30
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:43.833136+00:00
-- url     : https://prove2.me/theorems/892357b5-0a71-439d-802b-2823bb85f8be
-- title:
--   P2 M Formalism Basic Notions Examples  CD has Strict mul b9d1a3e90d30: P2 M Formalism Basic Notions Examples  CD has Strict mul b9d1a3e90d30
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD has Strict mul b9d1a3e90d30 construction uses the P2 M Formalism Basic Notions Examples  CD has Strict mul b9d1a3e90d30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L62-L72

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

theorem P2M_Formalism_BasicNotions_Examples__CD_hasStrict_mul_b9d1a3e90d30 (L M : 𝔸 × 𝔸 →L[ℝ] 𝔸) :
    HasStrictFDerivAt (fun p : 𝔸 × 𝔸 => logA 𝔸 (exp (L p) * exp (M p))) (L + M) (0 : 𝔸 × 𝔸) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«hasStrict_mul» := P2M_Formalism_BasicNotions_Examples__CD_hasStrict_mul_b9d1a3e90d30
