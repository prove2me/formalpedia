-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__tmul_algebraMap_931f1ce29a7a
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__tmul_algebraMap_931f1ce29a7a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:55.534114+00:00
-- url     : https://prove2.me/theorems/0d6aae06-e105-4477-9c4e-f3418ccd0f18
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  tmul algebra Map 931f1ce29a7a: P2 M Global Theory Companion Theory SW Pi Localization  tmul algebra Map 931f1ce29a7a
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  tmul algebra Map 931f1ce29a7a construction uses the P2 M Global Theory Companion Theory SW Pi Localization  tmul algebra Map 931f1ce29a7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramBlockOneFirstVectorFormula.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramBlockOneFirstVectorFormula.lean#L36-L39

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramBlockOneFirstVectorFormula
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
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__tmul_algebraMap_931f1ce29a7a (R : Type) [CommRing R] [Algebra F R] (u : R) (t : F) :
    u ⊗ₜ[F] (algebraMap F E t) = (u * algebraMap F R t) ⊗ₜ[F] (1 : E) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«tmul_algebraMap» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__tmul_algebraMap_931f1ce29a7a
