-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__hR_zero_left_101df9318131
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__hR_zero_left_101df9318131
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:15.032525+00:00
-- url     : https://prove2.me/theorems/8bd02fc7-a54d-402d-8205-dc5e1b39c702
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  h R zero left 101df9318131: P2 M Global Theory Companion Theory SW Pi Localization  h R zero left 101df9318131
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  h R zero left 101df9318131 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  h R zero left 101df9318131 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramBlockOneFirstVectorFormula.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramBlockOneFirstVectorFormula.lean#L23-L26

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__hR_zero_left_101df9318131 (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (y : Fin M → R ⊗[F] E) :
    hR R σ J (fun _ => 0) y = 0 := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«hR_zero_left» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__hR_zero_left_101df9318131
