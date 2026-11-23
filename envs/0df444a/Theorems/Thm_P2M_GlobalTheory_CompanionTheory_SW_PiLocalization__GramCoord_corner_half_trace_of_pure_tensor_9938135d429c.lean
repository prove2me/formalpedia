-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_corner_half_trace_of_pure_tensor_9938135d429c
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_corner_half_trace_of_pure_tensor_9938135d429c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:10.42482+00:00
-- url     : https://prove2.me/theorems/4e330626-0fe1-4607-9dee-65c488999e0e
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord corner half trace of pure tensor 9938135d429c: P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord corner half trace o
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord corner half trace of pure tensor 9938135d429c construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord corner half trace of pure tensor 9938135d429c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductMeasurable.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductMeasurable.lean#L18-L30

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_corner_half_trace_of_pure_tensor_9938135d429c (hfr : Module.finrank F E = 2) {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) (r : R)
    (h : S 0 0 = r ⊗ₜ[F] (1 : E)) : s0 R S = r := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«GramCoord».«corner_half_trace_of_pure_tensor» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_corner_half_trace_of_pure_tensor_9938135d429c
