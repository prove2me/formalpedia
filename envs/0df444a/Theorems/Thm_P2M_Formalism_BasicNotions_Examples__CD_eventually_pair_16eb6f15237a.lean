-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_eventually_pair_16eb6f15237a
-- name    : P2M_Formalism_BasicNotions_Examples__CD_eventually_pair_16eb6f15237a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:46.514845+00:00
-- url     : https://prove2.me/theorems/9b7baaa0-5a1e-4d78-a840-84662534c33f
-- title:
--   P2 M Formalism Basic Notions Examples  CD eventually pair 16eb6f15237a: P2 M Formalism Basic Notions Examples  CD eventually pair 16eb6f15237a
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD eventually pair 16eb6f15237a construction uses the P2 M Formalism Basic Notions Examples  CD eventually pair 16eb6f15237a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean#L88-L93

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

theorem P2M_Formalism_BasicNotions_Examples__CD_eventually_pair_16eb6f15237a {P : 𝔸 × 𝔸 → Prop} (h : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸), P p) :
    ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ → P (X, Y) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«eventually_pair» := P2M_Formalism_BasicNotions_Examples__CD_eventually_pair_16eb6f15237a
