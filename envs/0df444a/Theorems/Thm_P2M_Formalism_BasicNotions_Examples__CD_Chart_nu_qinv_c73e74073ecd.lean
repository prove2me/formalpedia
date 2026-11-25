-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_qinv_c73e74073ecd
-- name    : P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_qinv_c73e74073ecd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:36.585317+00:00
-- url     : https://prove2.me/theorems/ccb35370-a3fa-4b8e-b37c-c39c5cd1f0e0
-- title:
--   P2 M Formalism Basic Notions Examples  CD Chart nu qinv c73e74073ecd: P2 M Formalism Basic Notions Examples  CD Chart nu qinv c73e74073ecd
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD Chart nu qinv c73e74073ecd construction uses the P2 M Formalism Basic Notions Examples  CD Chart nu qinv c73e74073ecd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L149-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L149-L218

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

theorem P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_qinv_c73e74073ecd (hρ : 0 < ρ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) : ∃ δ > 0, QInv (C.nu ρ μ) ε δ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«Chart».«nu_qinv» := P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_qinv_c73e74073ecd
