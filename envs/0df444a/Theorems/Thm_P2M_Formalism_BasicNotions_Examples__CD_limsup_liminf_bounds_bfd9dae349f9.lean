-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_limsup_liminf_bounds_bfd9dae349f9
-- name    : P2M_Formalism_BasicNotions_Examples__CD_limsup_liminf_bounds_bfd9dae349f9
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:35.762738+00:00
-- url     : https://prove2.me/theorems/619e18dc-9111-4642-baed-66c1b26f8108
-- title:
--   P2 M Formalism Basic Notions Examples  CD limsup liminf bounds bfd9dae349f9: P2 M Formalism Basic Notions Examples  CD limsup liminf bounds bfd9dae349f9
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD limsup liminf bounds bfd9dae349f9 construction uses the P2 M Formalism Basic Notions Examples  CD limsup liminf bounds bfd9dae349f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LeOfEventuallyDown.lean#L102-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LeOfEventuallyDown.lean#L102-L147

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

theorem P2M_Formalism_BasicNotions_Examples__CD_limsup_liminf_bounds_bfd9dae349f9 {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hq : QInv nu ε δ) :
    ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      limsup (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤
        ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * L ∧
      ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * L ≤
        liminf (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«limsup_liminf_bounds» := P2M_Formalism_BasicNotions_Examples__CD_limsup_liminf_bounds_bfd9dae349f9
