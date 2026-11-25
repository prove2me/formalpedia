-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_le_of_eventually_up_99e470a03a01
-- name    : P2M_Formalism_BasicNotions_Examples__CD_le_of_eventually_up_99e470a03a01
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:05.015254+00:00
-- url     : https://prove2.me/theorems/a5c687d6-b32d-4032-b409-c4cf2e718e08
-- title:
--   P2 M Formalism Basic Notions Examples  CD le of eventually up 99e470a03a01: P2 M Formalism Basic Notions Examples  CD le of eventually up 99e470a03a01
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD le of eventually up 99e470a03a01 construction uses the P2 M Formalism Basic Notions Examples  CD le of eventually up 99e470a03a01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LeOfEventuallyDown.lean#L38-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LeOfEventuallyDown.lean#L38-L63

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

theorem P2M_Formalism_BasicNotions_Examples__CD_le_of_eventually_up_99e470a03a01 {ε δ : ℝ} (hε1 : ε < 1) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M : ℝ≥0∞) ≤ M' * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V))
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), nu (closedBall 0 r) ≤ M * lam (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : nu s ≤ M' * lam s := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«le_of_eventually_up» := P2M_Formalism_BasicNotions_Examples__CD_le_of_eventually_up_99e470a03a01
