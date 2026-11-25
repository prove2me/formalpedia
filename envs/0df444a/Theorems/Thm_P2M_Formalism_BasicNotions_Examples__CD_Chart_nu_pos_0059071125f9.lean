-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_pos_0059071125f9
-- name    : P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_pos_0059071125f9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:53.079003+00:00
-- url     : https://prove2.me/theorems/de8f4411-b31f-41df-be87-41061ab017fd
-- title:
--   P2 M Formalism Basic Notions Examples  CD Chart nu pos 0059071125f9: P2 M Formalism Basic Notions Examples  CD Chart nu pos 0059071125f9
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD Chart nu pos 0059071125f9 construction uses the P2 M Formalism Basic Notions Examples  CD Chart nu pos 0059071125f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L116-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L116-L146

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
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
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open Formalism.BasicNotions.Examples₂.CD.Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)
variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G)
variable [IsTopologicalGroup G] [μ.IsHaarMeasure]
include hR

theorem P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_pos_0059071125f9 (hρ : 0 < ρ) (r : ℝ) (hr : 0 < r) : 0 < C.nu ρ μ (closedBall (0 : V) r) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«Chart».«nu_pos» := P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_pos_0059071125f9
