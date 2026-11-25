-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_unit_tmul_7668c6c4ee16
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_unit_tmul_7668c6c4ee16
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:06:34.375497+00:00
-- url     : https://prove2.me/theorems/b636b07a-78e6-4cb2-a878-39334fa6ec98
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord unit tmul 7668c6c4ee16: P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord unit tmul 7668c6c4ee16
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord unit tmul 7668c6c4ee16 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Gram Coord unit tmul 7668c6c4ee16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductMeasurable.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductMeasurable.lean#L58-L62

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_unit_tmul_7668c6c4ee16 {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    {t : F} (ht : t ≠ 0) (u : Rˣ) :
    ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * (((u : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t)) : R ⊗[F] E) = 1 := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«GramCoord».«unit_tmul» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_unit_tmul_7668c6c4ee16
