-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__sigR_tmul_one_e4a1507eaac4
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__sigR_tmul_one_e4a1507eaac4
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:06.022782+00:00
-- url     : https://prove2.me/theorems/3b0d1407-dfb3-469e-8cd1-684c78284b44
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  sig R tmul one e4a1507eaac4: P2 M Global Theory Companion Theory SW Pi Localization  sig R tmul one e4a1507eaac4
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  sig R tmul one e4a1507eaac4 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  sig R tmul one e4a1507eaac4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramBlockOneFirstVectorFormula.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramBlockOneFirstVectorFormula.lean#L28-L30

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__sigR_tmul_one_e4a1507eaac4 (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (u : R) :
    sigR R σ (u ⊗ₜ[F] (1 : E)) = u ⊗ₜ[F] (1 : E) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«sigR_tmul_one» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__sigR_tmul_one_e4a1507eaac4
