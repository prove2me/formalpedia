-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_corner_half_trace_gram_cons_dc016762720f
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_corner_half_trace_gram_cons_dc016762720f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:58.621377+00:00
-- url     : https://prove2.me/theorems/776a8951-bbb4-4f3c-9c1a-2530d4ea9c85
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 corner half trace gram cons dc016762720f: P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 corner half trace gram cons dc
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 corner half trace gram cons dc016762720f construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 corner half trace gram cons dc016762720f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUnfold.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUnfold.lean#L38-L42

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureOrthogonalExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousHermScal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductIntegralStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductUnfold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_corner_half_trace_gram_cons_dc016762720f (σ : E →ₐ[F] E) {N n : ℕ} (J₂ : Matrix (Fin N) (Fin N) E)
    (y : Fin 1 → Fin N → R ⊗[F] E) (Z : Fin n → Fin N → R ⊗[F] E) :
    s0 R (gramR R σ J₂ (Fin.cons (y 0) Z : Fin (n + 1) → Fin N → R ⊗[F] E)) =
      s0 R (gramR R σ J₂ y) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«Unfold1».«corner_half_trace_gram_cons» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_corner_half_trace_gram_cons_dc016762720f
