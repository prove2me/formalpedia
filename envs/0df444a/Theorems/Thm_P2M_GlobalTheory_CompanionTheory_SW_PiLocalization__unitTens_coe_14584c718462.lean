-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__unitTens_coe_14584c718462
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__unitTens_coe_14584c718462
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:50.152598+00:00
-- url     : https://prove2.me/theorems/3dbab52a-36a7-4953-9a9a-4bf24ee638b8
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  unit Tens coe 14584c718462: P2 M Global Theory Companion Theory SW Pi Localization  unit Tens coe 14584c718462
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  unit Tens coe 14584c718462 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  unit Tens coe 14584c718462 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankOneFiberMeasureBlockExtension.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankOneFiberMeasureBlockExtension.lean#L51-L52

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__unitTens_coe_14584c718462 (u : Rˣ) :
    ((unitTens (F := F) (E := E) R u : (R ⊗[F] E)ˣ) : R ⊗[F] E) = (u : R) ⊗ₜ[F] (1 : E) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«unitTens_coe» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__unitTens_coe_14584c718462
