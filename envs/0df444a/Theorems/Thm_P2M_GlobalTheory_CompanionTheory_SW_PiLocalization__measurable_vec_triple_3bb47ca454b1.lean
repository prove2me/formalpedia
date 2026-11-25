-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__measurable_vec_triple_3bb47ca454b1
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__measurable_vec_triple_3bb47ca454b1
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:02.653819+00:00
-- url     : https://prove2.me/theorems/e06fdde3-e24d-41c7-854d-9541a2858094
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  measurable vec triple 3bb47ca454b1: P2 M Global Theory Companion Theory SW Pi Localization  measurable vec triple 3bb47ca454b1
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  measurable vec triple 3bb47ca454b1 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  measurable vec triple 3bb47ca454b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductFubini.lean#L74-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductFubini.lean#L74-L91

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductFubini
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology ProbabilityTheory
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__measurable_vec_triple_3bb47ca454b1 {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} :
    Measurable (fun p : K × (Fin n → K) × (Fin n → Fin M → K) =>
      (vec p.1 p.2.1 p.2.2 : Fin (n + 1) → Fin (M + 1) → K)) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«measurable_vec_triple» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__measurable_vec_triple_3bb47ca454b1
