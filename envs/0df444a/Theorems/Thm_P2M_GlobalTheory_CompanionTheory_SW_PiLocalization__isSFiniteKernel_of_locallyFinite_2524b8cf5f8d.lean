-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isSFiniteKernel_of_locallyFinite_2524b8cf5f8d
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isSFiniteKernel_of_locallyFinite_2524b8cf5f8d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:38.755571+00:00
-- url     : https://prove2.me/theorems/6e27db11-c9c4-47b2-b3cb-eb62f7cc8bf9
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  is SFinite Kernel of locally Finite 2524b8cf5f8d: P2 M Global Theory Companion Theory SW Pi Localization  is SFinite Kernel of locally Finite 25
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  is SFinite Kernel of locally Finite 2524b8cf5f8d construction uses the P2 M Global Theory Companion Theory SW Pi Localization  is SFinite Kernel of locally Finite 2524b8cf5f8d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductFubini.lean#L48-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductFubini.lean#L48-L72

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isSFiniteKernel_of_locallyFinite_2524b8cf5f8d {α β : Type} [MeasurableSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] [T2Space β] [SigmaCompactSpace β]
    (κ : Kernel α β) (h : ∀ a, IsLocallyFiniteMeasure (κ a)) : IsSFiniteKernel κ := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«isSFiniteKernel_of_locallyFinite» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isSFiniteKernel_of_locallyFinite_2524b8cf5f8d
