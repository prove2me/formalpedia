-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_apply_3ee47408ca0b
-- name    : P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_apply_3ee47408ca0b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:37.416261+00:00
-- url     : https://prove2.me/theorems/33f2b7a1-a62f-4a00-93f6-df607e80c72f
-- title:
--   P2 M Formalism Basic Notions Examples  CD Chart nu apply 3ee47408ca0b: P2 M Formalism Basic Notions Examples  CD Chart nu apply 3ee47408ca0b
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD Chart nu apply 3ee47408ca0b construction uses the P2 M Formalism Basic Notions Examples  CD Chart nu apply 3ee47408ca0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L83-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L83-L104

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
include hR

theorem P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_apply_3ee47408ca0b {s : Set V} (hs : MeasurableSet s) :
    C.nu ρ μ s = μ (C.expG '' (s ∩ ball 0 ρ)) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«Chart».«nu_apply» := P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_apply_3ee47408ca0b
