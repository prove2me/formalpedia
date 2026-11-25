-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold_measurable_vec_69241eff3c0e
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold_measurable_vec_69241eff3c0e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:53.19486+00:00
-- url     : https://prove2.me/theorems/569bceeb-6259-442b-aa5b-fae36936b1c4
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Unfold measurable vec 69241eff3c0e: P2 M Global Theory Companion Theory SW Pi Localization  Unfold measurable vec 69241eff3c0e
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Unfold measurable vec 69241eff3c0e construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Unfold measurable vec 69241eff3c0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductDensity.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductDensity.lean#L16-L26

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold_measurable_vec_69241eff3c0e {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} (α : K) :
    Measurable (fun p : (Fin n → K) × (Fin n → Fin M → K) => vec α p.1 p.2) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«Unfold».«measurable_vec» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold_measurable_vec_69241eff3c0e
