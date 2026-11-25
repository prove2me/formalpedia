-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_tendsto_ratio_7b967ab87425
-- name    : P2M_Formalism_BasicNotions_Examples__CD_tendsto_ratio_7b967ab87425
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:34.411804+00:00
-- url     : https://prove2.me/theorems/24a5272c-854a-4bfb-89ac-35d90a3ae878
-- title:
--   P2 M Formalism Basic Notions Examples  CD tendsto ratio 7b967ab87425: P2 M Formalism Basic Notions Examples  CD tendsto ratio 7b967ab87425
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD tendsto ratio 7b967ab87425 construction uses the P2 M Formalism Basic Notions Examples  CD tendsto ratio 7b967ab87425 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LeOfEventuallyDown.lean#L239-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LeOfEventuallyDown.lean#L239-L256

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
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
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]

theorem P2M_Formalism_BasicNotions_Examples__CD_tendsto_ratio_7b967ab87425 {c : ℝ≥0∞}
    (hup : ∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s)
    (hdown : ∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s)
    (S : ℝ → Set V) (hS : ∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), S r ⊆ ball 0 δ)
    (hS0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) :
    Tendsto (fun r => nu (S r) / lam (S r)) (𝓝[>] 0) (𝓝 c) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«tendsto_ratio» := P2M_Formalism_BasicNotions_Examples__CD_tendsto_ratio_7b967ab87425
