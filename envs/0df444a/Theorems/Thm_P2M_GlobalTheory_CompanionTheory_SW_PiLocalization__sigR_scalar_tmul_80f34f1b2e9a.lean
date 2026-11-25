-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__sigR_scalar_tmul_80f34f1b2e9a
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__sigR_scalar_tmul_80f34f1b2e9a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:03.237266+00:00
-- url     : https://prove2.me/theorems/8eebb4d8-e0dc-4d1a-897a-12eab6040056
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  sig R scalar tmul 80f34f1b2e9a: P2 M Global Theory Companion Theory SW Pi Localization  sig R scalar tmul 80f34f1b2e9a
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  sig R scalar tmul 80f34f1b2e9a construction uses the P2 M Global Theory Companion Theory SW Pi Localization  sig R scalar tmul 80f34f1b2e9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductFold.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductFold.lean#L21-L23

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__sigR_scalar_tmul_80f34f1b2e9a (σ : E →ₐ[F] E) (α : R) :
    sigR R σ (α ⊗ₜ[F] (1 : E)) = α ⊗ₜ[F] (1 : E) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«sigR_scalar_tmul» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__sigR_scalar_tmul_80f34f1b2e9a
