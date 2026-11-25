-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__measurable_vec_a3e9d532eadc
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__measurable_vec_a3e9d532eadc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:02.045481+00:00
-- url     : https://prove2.me/theorems/c60ec774-6155-49f6-9308-b92887105de2
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  measurable vec a3e9d532eadc: P2 M Global Theory Companion Theory SW Pi Localization  measurable vec a3e9d532eadc
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  measurable vec a3e9d532eadc construction uses the P2 M Global Theory Companion Theory SW Pi Localization  measurable vec a3e9d532eadc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductNormalization.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductNormalization.lean#L14-L26

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductMeasurableStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductNormalization
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__measurable_vec_a3e9d532eadc {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} (α : K) (c : Fin n → K) :
    Measurable (fun X : Fin n → Fin M → K => vec α c X) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«measurable_vec» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__measurable_vec_a3e9d532eadc
