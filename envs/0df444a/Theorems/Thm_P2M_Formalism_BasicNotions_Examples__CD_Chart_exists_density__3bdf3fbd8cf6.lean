-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_density__3bdf3fbd8cf6
-- name    : P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_density__3bdf3fbd8cf6
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:30.192327+00:00
-- url     : https://prove2.me/theorems/c4c187d0-096e-478b-821f-3c0e681af860
-- title:
--   P2 M Formalism Basic Notions Examples  CD Chart exists density  3bdf3fbd8cf6: P2 M Formalism Basic Notions Examples  CD Chart exists density  3bdf3fbd8cf6
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD Chart exists density  3bdf3fbd8cf6 construction uses the P2 M Formalism Basic Notions Examples  CD Chart exists density  3bdf3fbd8cf6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L252-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L252-L270

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

theorem P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_density__3bdf3fbd8cf6 {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G]
    (C : Chart V G) (_hfd : FiniteDimensional ℝ V) (mV : MeasurableSpace V) (_hbV : BorelSpace V)
    (mG : MeasurableSpace G) (_hbG : BorelSpace G) (_hG : IsTopologicalGroup G)
    (μ : Measure G) (_hμ : μ.IsHaarMeasure) (lam : Measure V) (_hlam : lam.IsAddHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : ℝ → Set V, (∀ r, MeasurableSet (S r)) →
      (∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ X ∈ S r, ‖(X : 𝔸)‖ < δ) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) →
      Tendsto (fun r => μ {g | ∃ X ∈ S r, C.mat g = exp ((X : V) : 𝔸)} / lam (S r)) (𝓝[>] 0) (𝓝 c) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«Chart».«exists_density'» := P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_density__3bdf3fbd8cf6
