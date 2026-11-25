-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__corner_half_trace_of_pure_tensor_c407ddf04396
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__corner_half_trace_of_pure_tensor_c407ddf04396
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:17.30473+00:00
-- url     : https://prove2.me/theorems/866d7cd7-b54e-442a-8991-7b46e9c3f11f
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  corner half trace of pure tensor c407ddf04396: P2 M Global Theory Companion Theory SW Pi Localization  corner half trace of pure tensor c407ddf0
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  corner half trace of pure tensor c407ddf04396 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  corner half trace of pure tensor c407ddf04396 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductFold.lean#L33-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductFold.lean#L33-L46

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductMeasurableStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductFold
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_corner_half_trace_of_pure_tensor_9938135d429c

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__corner_half_trace_of_pure_tensor_c407ddf04396 [CharZero F] {d : ℕ} (b : Module.Basis (Fin d) F E) (hd : Module.finrank F E = 2)
    (x : R) (S : Matrix (Fin (0 + 1)) (Fin (0 + 1)) (R ⊗[F] E)) (h : S 0 0 = x ⊗ₜ[F] (1 : E)) :
    s0 R S = x := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«corner_half_trace_of_pure_tensor» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__corner_half_trace_of_pure_tensor_c407ddf04396
