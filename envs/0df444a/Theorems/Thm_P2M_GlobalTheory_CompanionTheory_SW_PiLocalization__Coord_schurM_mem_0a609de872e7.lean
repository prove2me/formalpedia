-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Coord_schurM_mem_0a609de872e7
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Coord_schurM_mem_0a609de872e7
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:03:51.009254+00:00
-- url     : https://prove2.me/theorems/7f162467-9d8e-414a-ab9b-37eaa84c8b39
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Coord schur M mem 0a609de872e7: P2 M Global Theory Companion Theory SW Pi Localization  Coord schur M mem 0a609de872e7
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Coord schur M mem 0a609de872e7 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Coord schur M mem 0a609de872e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductIntegral.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductIntegral.lean#L13-L23

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductIntegral
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Coord_schurM_mem_0a609de872e7 {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hinv : ∀ y : R ⊗[F] E, sigR R σ (sigR R σ y) = y) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : HermR R σ (n + 1)) :
    schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«Coord».«schurM_mem» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Coord_schurM_mem_0a609de872e7
