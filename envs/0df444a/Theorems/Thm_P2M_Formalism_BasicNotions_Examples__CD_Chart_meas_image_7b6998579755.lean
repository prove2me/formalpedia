-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_meas_image_7b6998579755
-- name    : P2M_Formalism_BasicNotions_Examples__CD_Chart_meas_image_7b6998579755
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:58.035463+00:00
-- url     : https://prove2.me/theorems/7b342b49-3c91-4820-9ede-a142d9a7d7f4
-- title:
--   P2 M Formalism Basic Notions Examples  CD Chart meas image 7b6998579755: P2 M Formalism Basic Notions Examples  CD Chart meas image 7b6998579755
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD Chart meas image 7b6998579755 construction uses the P2 M Formalism Basic Notions Examples  CD Chart meas image 7b6998579755 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L71-L75

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
include hR

theorem P2M_Formalism_BasicNotions_Examples__CD_Chart_meas_image_7b6998579755 {s : Set V} (hs : MeasurableSet s) (hsub : s ⊆ ball 0 ρ) :
    MeasurableSet (C.expG '' s) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«Chart».«meas_image» := P2M_Formalism_BasicNotions_Examples__CD_Chart_meas_image_7b6998579755
