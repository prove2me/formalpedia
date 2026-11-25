-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_hasStrict_exp_comp_abeda0874ee6
-- name    : P2M_Formalism_BasicNotions_Examples__CD_hasStrict_exp_comp_abeda0874ee6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:33.40511+00:00
-- url     : https://prove2.me/theorems/33aff0cf-fa05-4947-846d-3ea11fd7cd13
-- title:
--   P2 M Formalism Basic Notions Examples  CD has Strict exp comp abeda0874ee6: P2 M Formalism Basic Notions Examples  CD has Strict exp comp abeda0874ee6
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD has Strict exp comp abeda0874ee6 construction uses the P2 M Formalism Basic Notions Examples  CD has Strict exp comp abeda0874ee6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L53-L60

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

theorem P2M_Formalism_BasicNotions_Examples__CD_hasStrict_exp_comp_abeda0874ee6 (L : 𝔸 × 𝔸 →L[ℝ] 𝔸) :
    HasStrictFDerivAt (fun p : 𝔸 × 𝔸 => exp (L p)) L (0 : 𝔸 × 𝔸) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«hasStrict_exp_comp» := P2M_Formalism_BasicNotions_Examples__CD_hasStrict_exp_comp_abeda0874ee6
