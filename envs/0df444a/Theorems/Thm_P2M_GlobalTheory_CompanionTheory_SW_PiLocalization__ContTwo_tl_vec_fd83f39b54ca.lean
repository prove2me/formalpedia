-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_tl_vec_fd83f39b54ca
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_tl_vec_fd83f39b54ca
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:03:32.978+00:00
-- url     : https://prove2.me/theorems/56598d34-885e-4fe0-b257-921df8adaf80
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Cont Two tl vec fd83f39b54ca: P2 M Global Theory Companion Theory SW Pi Localization  Cont Two tl vec fd83f39b54ca
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Cont Two tl vec fd83f39b54ca construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Cont Two tl vec fd83f39b54ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUniqueness.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUniqueness.lean#L21-L24

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_tl_vec_fd83f39b54ca {K : Type} [Zero K] {M n : ℕ} (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) :
    tl (vec α c X) = X := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«ContTwo».«tl_vec» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_tl_vec_fd83f39b54ca
