-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_fin_cons_fc68d0337b48
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_fin_cons_fc68d0337b48
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:33.968915+00:00
-- url     : https://prove2.me/theorems/a0289f87-c29a-498e-8bf2-101aebfe53d9
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 measurable fin cons fc68d0337b48: P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 measurable fin cons fc68d0337b48
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 measurable fin cons fc68d0337b48 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 measurable fin cons fc68d0337b48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUnfold.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUnfold.lean#L20-L26

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_fin_cons_fc68d0337b48 {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] {n : ℕ}
    {f : Ω → A} {g : Ω → Fin n → A} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p => (Fin.cons (f p) (g p) : Fin (n + 1) → A) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«Unfold1».«measurable_fin_cons» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_fin_cons_fc68d0337b48
