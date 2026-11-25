-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__continuous_vec_8c5d52ef9dc7
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__continuous_vec_8c5d52ef9dc7
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:06.838451+00:00
-- url     : https://prove2.me/theorems/5793faff-5da3-46d0-9792-8b85eaafc7d7
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  continuous vec 8c5d52ef9dc7: P2 M Global Theory Companion Theory SW Pi Localization  continuous vec 8c5d52ef9dc7
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  continuous vec 8c5d52ef9dc7 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  continuous vec 8c5d52ef9dc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductScaling.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductScaling.lean#L56-L64

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__continuous_vec_8c5d52ef9dc7 {K : Type} [TopologicalSpace K] [Zero K] {M n : ℕ} (u : K) (c : Fin n → K) :
    Continuous (fun X : Fin n → Fin M → K => vec u c X) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«continuous_vec» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__continuous_vec_8c5d52ef9dc7
