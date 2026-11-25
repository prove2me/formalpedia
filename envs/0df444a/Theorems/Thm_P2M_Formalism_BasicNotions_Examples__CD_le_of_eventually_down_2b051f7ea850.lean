-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_le_of_eventually_down_2b051f7ea850
-- name    : P2M_Formalism_BasicNotions_Examples__CD_le_of_eventually_down_2b051f7ea850
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:51.821814+00:00
-- url     : https://prove2.me/theorems/c7745983-99fd-497a-97cf-950704eb28fd
-- title:
--   P2 M Formalism Basic Notions Examples  CD le of eventually down 2b051f7ea850: P2 M Formalism Basic Notions Examples  CD le of eventually down 2b051f7ea850
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD le of eventually down 2b051f7ea850 construction uses the P2 M Formalism Basic Notions Examples  CD le of eventually down 2b051f7ea850 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LeOfEventuallyDown.lean#L65-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LeOfEventuallyDown.lean#L65-L91

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

theorem P2M_Formalism_BasicNotions_Examples__CD_le_of_eventually_down_2b051f7ea850 {ε δ : ℝ} (hε0 : 0 < ε) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M' : ℝ≥0∞) * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) ≤ M)
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), M * lam (closedBall 0 r) ≤ nu (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : M' * lam s ≤ nu s := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«le_of_eventually_down» := P2M_Formalism_BasicNotions_Examples__CD_le_of_eventually_down_2b051f7ea850
