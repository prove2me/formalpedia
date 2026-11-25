-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_gram_symm_862d9e99a9ef
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_gram_symm_862d9e99a9ef
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:22.325326+00:00
-- url     : https://prove2.me/theorems/2b6e055b-42c0-407c-806b-70d5dac1e92a
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord gram symm 862d9e99a9ef: P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord gram symm 862d9e99a9ef
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord gram symm 862d9e99a9ef construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord gram symm 862d9e99a9ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductMeasurable.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductMeasurable.lean#L34-L43

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramBlockOneFirstVectorFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
variable [NumberField E]

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_gram_symm_862d9e99a9ef (σ : E →ₐ[F] E) (hinv : ∀ y, sigR R σ (sigR R σ y) = y) {M n : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) (p q : Fin n) :
    sigR R σ (gramR R σ J X q p) = gramR R σ J X p q := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«GramCoord».«gram_symm» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_gram_symm_862d9e99a9ef
