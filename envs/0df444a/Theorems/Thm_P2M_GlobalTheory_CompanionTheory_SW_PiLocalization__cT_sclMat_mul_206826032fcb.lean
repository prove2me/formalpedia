-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__cT_sclMat_mul_206826032fcb
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__cT_sclMat_mul_206826032fcb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:23.047744+00:00
-- url     : https://prove2.me/theorems/df6c7b08-0cb6-40ec-ae45-cbf62f681fb9
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  c T scl Mat mul 206826032fcb: P2 M Global Theory Companion Theory SW Pi Localization  c T scl Mat mul 206826032fcb
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  c T scl Mat mul 206826032fcb construction uses the P2 M Global Theory Companion Theory SW Pi Localization  c T scl Mat mul 206826032fcb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankOneFiberMeasureBlockExtension.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankOneFiberMeasureBlockExtension.lean#L61-L73

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__cT_sclMat_mul_206826032fcb (σ : E →ₐ[F] E) (u s : R) :
    ((hermScal R σ (u ^ 2 * s) : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) (sclMat (F := F) (E := E) R u) *
        ((hermScal R σ s : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        sclMat (F := F) (E := E) R u := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«cT_sclMat_mul» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__cT_sclMat_mul_206826032fcb
