-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_schurM_mem_f18186865e22
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_schurM_mem_f18186865e22
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:36.540979+00:00
-- url     : https://prove2.me/theorems/d1881c48-5cf2-41a6-b994-a0575cca735d
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord schur M mem f18186865e22: P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord schur M mem f18186865e22
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord schur M mem f18186865e22 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord schur M mem f18186865e22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductMeasurable.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductMeasurable.lean#L45-L54

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_schurM_mem_f18186865e22 (σ : E →ₐ[F] E) (hinv : ∀ y, sigR R σ (sigR R σ y) = y) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : HermR R σ (n + 1)) :
    schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«GramCoord».«schurM_mem» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_schurM_mem_f18186865e22
