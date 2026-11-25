-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_vec_0b2fc4931bd4
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_vec_0b2fc4931bd4
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:03.8164+00:00
-- url     : https://prove2.me/theorems/8efbdfe8-1918-4a51-b549-83ea0878e9b9
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Cont Two continuous vec 0b2fc4931bd4: P2 M Global Theory Companion Theory SW Pi Localization  Cont Two continuous vec 0b2fc4931bd4
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Cont Two continuous vec 0b2fc4931bd4 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Cont Two continuous vec 0b2fc4931bd4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUniqueness.lean#L31-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUniqueness.lean#L31-L46

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_vec_0b2fc4931bd4 {K : Type} [Zero K] [TopologicalSpace K] {M n : ℕ} :
    Continuous (fun p : K × (Fin n → K) × (Fin n → Fin M → K) => vec p.1 p.2.1 p.2.2) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«ContTwo».«continuous_vec» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_vec_0b2fc4931bd4
