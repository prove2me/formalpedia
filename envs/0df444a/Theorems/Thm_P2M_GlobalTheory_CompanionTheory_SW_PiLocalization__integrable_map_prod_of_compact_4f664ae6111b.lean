-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__integrable_map_prod_of_compact_4f664ae6111b
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__integrable_map_prod_of_compact_4f664ae6111b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:40.116602+00:00
-- url     : https://prove2.me/theorems/e3c5f837-0e0d-4e39-a378-3b9420fe2b74
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  integrable map prod of compact 4f664ae6111b: P2 M Global Theory Companion Theory SW Pi Localization  integrable map prod of compact 4f664ae6111b
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  integrable map prod of compact 4f664ae6111b construction uses the P2 M Global Theory Companion Theory SW Pi Localization  integrable map prod of compact 4f664ae6111b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductScaling.lean#L15-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductScaling.lean#L15-L49

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__integrable_map_prod_of_compact_4f664ae6111b {A B W : Type} [TopologicalSpace A] [MeasurableSpace A]
    [OpensMeasurableSpace A] [T2Space A] [TopologicalSpace B] [MeasurableSpace B]
    [OpensMeasurableSpace B] [T2Space B] [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] [IsFiniteMeasureOnCompacts μ]
    [IsFiniteMeasureOnCompacts ν] (f : A × B → W) (hf : Measurable f) (φ : W → ℝ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (C₁ : Set A) (C₂ : Set B)
    (h₁ : IsCompact C₁) (h₂ : IsCompact C₂)
    (hs : ∀ᵐ y ∂μ, ∀ X, φ (f (y, X)) ≠ 0 → y ∈ C₁ ∧ X ∈ C₂) (k : ℝ≥0) :
    Integrable φ (k • (μ.prod ν).map f) ∧
      ∫ v, φ v ∂(k • (μ.prod ν).map f) = (k : ℝ) * ∫ y, ∫ X, φ (f (y, X)) ∂ν ∂μ := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«integrable_map_prod_of_compact» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__integrable_map_prod_of_compact_4f664ae6111b
