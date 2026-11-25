-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_distortion_ba7d2bd37f11
-- name    : P2M_Formalism_BasicNotions_Examples__CD_distortion_ba7d2bd37f11
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:39.583883+00:00
-- url     : https://prove2.me/theorems/b1f19b7f-f78e-4d39-b3b4-6205474c9891
-- title:
--   P2 M Formalism Basic Notions Examples  CD distortion ba7d2bd37f11: P2 M Formalism Basic Notions Examples  CD distortion ba7d2bd37f11
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD distortion ba7d2bd37f11 construction uses the P2 M Formalism Basic Notions Examples  CD distortion ba7d2bd37f11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L113-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L113-L155

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

theorem P2M_Formalism_BasicNotions_Examples__CD_distortion_ba7d2bd37f11 {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
    (exp (F1 (X, Y)) = exp (-X) * exp (X + Y) ∧ ‖F1 (X, Y) - Y‖ ≤ ε * ‖Y‖) ∧
    (exp (F2 (X, Y)) = exp X * exp Y ∧ ‖F2 (X, Y) - X - Y‖ ≤ ε * ‖Y‖) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«distortion» := P2M_Formalism_BasicNotions_Examples__CD_distortion_ba7d2bd37f11
