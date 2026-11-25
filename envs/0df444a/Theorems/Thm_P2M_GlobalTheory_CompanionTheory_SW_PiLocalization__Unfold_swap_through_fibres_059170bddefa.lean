-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold_swap_through_fibres_059170bddefa
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold_swap_through_fibres_059170bddefa
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:26.239801+00:00
-- url     : https://prove2.me/theorems/0c7cfd12-6333-4ef6-b6d6-291b1512d5a3
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Unfold swap through fibres 059170bddefa: P2 M Global Theory Companion Theory SW Pi Localization  Unfold swap through fibres 059170bddefa
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Unfold swap through fibres 059170bddefa construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Unfold swap through fibres 059170bddefa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductDensity.lean#L28-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductDensity.lean#L28-L73

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerate
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductUnfoldStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductFoldStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold_swap_through_fibres_059170bddefa {Y C X H : Type} [MeasurableSpace Y] [MeasurableSpace C] [MeasurableSpace X]
    [MeasurableSpace H] (μ₁ : Measure Y) (μc : Measure C) (μ : Measure X) (ν : Measure H)
    [SFinite μ₁] [SFinite μc] [SFinite μ] (U : Set X) (W : Set H) (hW : MeasurableSet W)
    (m : H → Measure X) (hm : ∀ S, SFinite (m S)) (hoff : ∀ S, S ∉ W → m S = 0)
    (hfib : ∀ ψ : X → ℝ≥0∞, Measurable ψ → ∫⁻ v in U, ψ v ∂μ = ∫⁻ S, ∫⁻ v, ψ v ∂(m S) ∂ν)
    (f : Y → C → X → ℝ≥0∞) (hf : Measurable fun p : Y × C × X => f p.1 p.2.1 p.2.2) :
    ∫⁻ y, ∫⁻ c, ∫⁻ S in W, ∫⁻ v, f y c v ∂(m S) ∂ν ∂μc ∂μ₁ =
      ∫⁻ c, ∫⁻ S in W, ∫⁻ y, ∫⁻ v, f y c v ∂(m S) ∂μ₁ ∂ν ∂μc := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«Unfold».«swap_through_fibres» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold_swap_through_fibres_059170bddefa
