-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__tmul_one_mul_inclR_658628a98b31
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__tmul_one_mul_inclR_658628a98b31
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:26.653434+00:00
-- url     : https://prove2.me/theorems/f9b8ec0e-3ad6-4f93-9322-621345dd30e3
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  tmul one mul incl R 658628a98b31: P2 M Global Theory Companion Theory SW Pi Localization  tmul one mul incl R 658628a98b31
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  tmul one mul incl R 658628a98b31 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  tmul one mul incl R 658628a98b31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramBlockOneFirstVectorFormula.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramBlockOneFirstVectorFormula.lean#L32-L34

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__tmul_one_mul_inclR_658628a98b31 (R : Type) [CommRing R] [Algebra F R] (u : R) (e : E) :
    (u ⊗ₜ[F] (1 : E)) * inclR R e = u ⊗ₜ[F] e := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«tmul_one_mul_inclR» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__tmul_one_mul_inclR_658628a98b31
