-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__hR_blockOne_cons_7313ef7402fc
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__hR_blockOne_cons_7313ef7402fc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:11.353375+00:00
-- url     : https://prove2.me/theorems/b7a8c049-2396-4fa9-b3f4-b960d5e94261
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  h R block One cons 7313ef7402fc: P2 M Global Theory Companion Theory SW Pi Localization  h R block One cons 7313ef7402fc
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  h R block One cons 7313ef7402fc construction uses the P2 M Global Theory Companion Theory SW Pi Localization  h R block One cons 7313ef7402fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramBlockOneFirstVectorFormula.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramBlockOneFirstVectorFormula.lean#L15-L21

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__hR_blockOne_cons_7313ef7402fc (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (t : E) (x₀ y₀ : R ⊗[F] E) (x y : Fin M → R ⊗[F] E) :
    hR R σ (blockOne t J) (Fin.cons x₀ x : Fin (M + 1) → R ⊗[F] E) (Fin.cons y₀ y) =
      sigR R σ x₀ * inclR R t * y₀ + hR R σ J x y := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«hR_blockOne_cons» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__hR_blockOne_cons_7313ef7402fc
