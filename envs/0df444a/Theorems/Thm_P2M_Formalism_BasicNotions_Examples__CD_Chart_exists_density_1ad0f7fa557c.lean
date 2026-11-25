-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_density_1ad0f7fa557c
-- name    : P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_density_1ad0f7fa557c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:10.76366+00:00
-- url     : https://prove2.me/theorems/257cebcb-b713-484e-9048-e0390f1b9c05
-- title:
--   P2 M Formalism Basic Notions Examples  CD Chart exists density 1ad0f7fa557c: P2 M Formalism Basic Notions Examples  CD Chart exists density 1ad0f7fa557c
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD Chart exists density 1ad0f7fa557c construction uses the P2 M Formalism Basic Notions Examples  CD Chart exists density 1ad0f7fa557c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L220-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L220-L248

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_exists_density_03e233a4d5e1

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

theorem P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_density_1ad0f7fa557c (lam : Measure V) [lam.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : ℝ → Set V, (∀ r, MeasurableSet (S r)) →
      (∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), S r ⊆ ball 0 δ) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) →
      Tendsto (fun r => μ (C.img (S r)) / lam (S r)) (𝓝[>] 0) (𝓝 c) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«Chart».«exists_density» := P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_density_1ad0f7fa557c
