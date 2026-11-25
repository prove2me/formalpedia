-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_tl_6db6ebf34396
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_tl_6db6ebf34396
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:04.826745+00:00
-- url     : https://prove2.me/theorems/9a9540dd-b2b0-40eb-8115-9fc9bca05f7b
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Cont Two continuous tl 6db6ebf34396: P2 M Global Theory Companion Theory SW Pi Localization  Cont Two continuous tl 6db6ebf34396
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Cont Two continuous tl 6db6ebf34396 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Cont Two continuous tl 6db6ebf34396 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUniqueness.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUniqueness.lean#L26-L29

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermFormPulledBackCombinationsExpandMonomials
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductUniqueness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_tl_6db6ebf34396 {K : Type} [TopologicalSpace K] {M n : ℕ} :
    Continuous (tl : (Fin (n + 1) → Fin (M + 1) → K) → Fin n → Fin M → K) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«ContTwo».«continuous_tl» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_tl_6db6ebf34396
