-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isSFiniteKernel_of_forall_univ_lt_top_f4df5b9f1781
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isSFiniteKernel_of_forall_univ_lt_top_f4df5b9f1781
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:33.812853+00:00
-- url     : https://prove2.me/theorems/7b833afa-f2cc-41bb-832c-40c4c5754a7c
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  is SFinite Kernel of forall univ lt top f4df5b9f1781: P2 M Global Theory Companion Theory SW Pi Localization  is SFinite Kernel of forall univ l
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  is SFinite Kernel of forall univ lt top f4df5b9f1781 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  is SFinite Kernel of forall univ lt top f4df5b9f1781 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductFubini.lean#L13-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductFubini.lean#L13-L46

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isSFiniteKernel_of_forall_univ_lt_top_f4df5b9f1781 {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (η : Kernel α β) (h : ∀ a, η a Set.univ < ⊤) : IsSFiniteKernel η := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«isSFiniteKernel_of_forall_univ_lt_top» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isSFiniteKernel_of_forall_univ_lt_top_f4df5b9f1781
