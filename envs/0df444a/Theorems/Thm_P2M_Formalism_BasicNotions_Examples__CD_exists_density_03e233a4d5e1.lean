-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_exists_density_03e233a4d5e1
-- name    : P2M_Formalism_BasicNotions_Examples__CD_exists_density_03e233a4d5e1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:28.916785+00:00
-- url     : https://prove2.me/theorems/b282af54-e1e9-49b9-92bb-0462e9be8ec5
-- title:
--   P2 M Formalism Basic Notions Examples  CD exists density 03e233a4d5e1: P2 M Formalism Basic Notions Examples  CD exists density 03e233a4d5e1
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD exists density 03e233a4d5e1 construction uses the P2 M Formalism Basic Notions Examples  CD exists density 03e233a4d5e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LeOfEventuallyDown.lean#L149-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LeOfEventuallyDown.lean#L149-L237

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

theorem P2M_Formalism_BasicNotions_Examples__CD_exists_density_03e233a4d5e1
    (hq : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, QInv nu ε δ)
    (hpos : ∀ r > 0, 0 < nu (closedBall (0 : V) r)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s) ∧
      (∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«exists_density» := P2M_Formalism_BasicNotions_Examples__CD_exists_density_03e233a4d5e1
