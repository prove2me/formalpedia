-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_tmul_one_568389719e18
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_tmul_one_568389719e18
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:03:30.650794+00:00
-- url     : https://prove2.me/theorems/093eee59-8c0b-4753-8db0-fc458d9b89c0
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Cont Two continuous tmul one 568389719e18: P2 M Global Theory Companion Theory SW Pi Localization  Cont Two continuous tmul one 568389719e18
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Cont Two continuous tmul one 568389719e18 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Cont Two continuous tmul one 568389719e18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUniqueness.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUniqueness.lean#L60-L68

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_tmul_one_568389719e18 {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (fun α : R => α ⊗ₜ[F] (1 : E)) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«ContTwo».«continuous_tmul_one» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_tmul_one_568389719e18
