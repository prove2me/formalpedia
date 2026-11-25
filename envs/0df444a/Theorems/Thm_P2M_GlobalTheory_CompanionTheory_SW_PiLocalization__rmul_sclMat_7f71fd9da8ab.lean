-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__rmul_sclMat_7f71fd9da8ab
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__rmul_sclMat_7f71fd9da8ab
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:20.757183+00:00
-- url     : https://prove2.me/theorems/cafea5a8-7e13-426f-89ef-873e311c1bae
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  rmul scl Mat 7f71fd9da8ab: P2 M Global Theory Companion Theory SW Pi Localization  rmul scl Mat 7f71fd9da8ab
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  rmul scl Mat 7f71fd9da8ab construction uses the P2 M Global Theory Companion Theory SW Pi Localization  rmul scl Mat 7f71fd9da8ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankOneFiberMeasureBlockExtension.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankOneFiberMeasureBlockExtension.lean#L54-L59

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__rmul_sclMat_7f71fd9da8ab {M : ℕ} (X : Fin 1 → Fin M → R ⊗[F] E) (u : R) :
    rmul R X (sclMat (F := F) (E := E) R u) = scl (u ⊗ₜ[F] (1 : E)) X := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«rmul_sclMat» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__rmul_sclMat_7f71fd9da8ab
