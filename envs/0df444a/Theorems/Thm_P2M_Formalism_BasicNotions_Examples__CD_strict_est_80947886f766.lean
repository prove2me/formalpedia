-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_strict_est_80947886f766
-- name    : P2M_Formalism_BasicNotions_Examples__CD_strict_est_80947886f766
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:41.87082+00:00
-- url     : https://prove2.me/theorems/23f0f759-54ac-473b-ba34-c8cdc121bb0b
-- title:
--   P2 M Formalism Basic Notions Examples  CD strict est 80947886f766: P2 M Formalism Basic Notions Examples  CD strict est 80947886f766
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD strict est 80947886f766 construction uses the P2 M Formalism Basic Notions Examples  CD strict est 80947886f766 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L95-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L95-L111

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

theorem P2M_Formalism_BasicNotions_Examples__CD_strict_est_80947886f766 {F : 𝔸 × 𝔸 → 𝔸} {F' : 𝔸 × 𝔸 →L[ℝ] 𝔸} (hF : HasStrictFDerivAt F F' 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
      ‖F (X, Y) - F (X, 0) - F' (0, Y)‖ ≤ ε * ‖Y‖ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«strict_est» := P2M_Formalism_BasicNotions_Examples__CD_strict_est_80947886f766
