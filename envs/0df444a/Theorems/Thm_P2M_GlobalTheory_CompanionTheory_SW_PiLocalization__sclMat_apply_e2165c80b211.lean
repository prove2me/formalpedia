-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__sclMat_apply_e2165c80b211
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__sclMat_apply_e2165c80b211
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:31.146696+00:00
-- url     : https://prove2.me/theorems/3ce9fb64-2b38-4064-97d6-0e1f0dde3f99
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  scl Mat apply e2165c80b211: P2 M Global Theory Companion Theory SW Pi Localization  scl Mat apply e2165c80b211
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  scl Mat apply e2165c80b211 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  scl Mat apply e2165c80b211 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankOneFiberMeasureBlockExtension.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankOneFiberMeasureBlockExtension.lean#L45-L46

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarModularCharacterOfContinuousAction
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RankOneFiberMeasureBlockExtension
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__sclMat_apply_e2165c80b211 (u : R) (i j : Fin 1) :
    sclMat (F := F) (E := E) R u i j = u ⊗ₜ[F] (1 : E) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«sclMat_apply» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__sclMat_apply_e2165c80b211
