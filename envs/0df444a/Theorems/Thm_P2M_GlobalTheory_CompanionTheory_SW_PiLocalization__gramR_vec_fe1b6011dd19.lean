-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__gramR_vec_fe1b6011dd19
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__gramR_vec_fe1b6011dd19
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:06.499536+00:00
-- url     : https://prove2.me/theorems/e04f4696-ff45-41d3-aa96-37c743d13d98
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  gram R vec fe1b6011dd19: P2 M Global Theory Companion Theory SW Pi Localization  gram R vec fe1b6011dd19
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  gram R vec fe1b6011dd19 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  gram R vec fe1b6011dd19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramBlockOneFirstVectorFormula.lean#L41-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramBlockOneFirstVectorFormula.lean#L41-L61

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__gramR_vec_fe1b6011dd19 (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] (u : R)
    (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) 0 0 =
        (u ^ 2 * algebraMap F R t) ⊗ₜ[F] (1 : E) ∧
      (∀ j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) 0 j.succ =
        (u ⊗ₜ[F] (algebraMap F E t)) * c j) ∧
      ∀ i j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) i.succ j.succ =
        sigR R σ (c i) * inclR R (algebraMap F E t) * c j + gramR R σ J X i j := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«gramR_vec» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__gramR_vec_fe1b6011dd19
