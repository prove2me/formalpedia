-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__gramR_scl_tmul_f342e5ccde38
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__gramR_scl_tmul_f342e5ccde38
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:48.571162+00:00
-- url     : https://prove2.me/theorems/cbdd4a3b-a60f-4475-8adc-9163962b2996
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  gram R scl tmul f342e5ccde38: P2 M Global Theory Companion Theory SW Pi Localization  gram R scl tmul f342e5ccde38
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  gram R scl tmul f342e5ccde38 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  gram R scl tmul f342e5ccde38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductFold.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductFold.lean#L25-L31

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductMeasurableStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductFold
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
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__gramR_scl_tmul_f342e5ccde38 (σ : E →ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (α : R)
    (y : Fin 1 → Fin N → R ⊗[F] E) (i j : Fin 1) :
    gramR R σ J (scl (α ⊗ₜ[F] (1 : E)) y) i j =
      (α ⊗ₜ[F] (1 : E)) * (α ⊗ₜ[F] (1 : E)) * gramR R σ J y i j := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«gramR_scl_tmul» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__gramR_scl_tmul_f342e5ccde38
