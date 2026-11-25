-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__nnreal_eq_of_smul_haar_89aee63d41dc
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__nnreal_eq_of_smul_haar_89aee63d41dc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:17.370008+00:00
-- url     : https://prove2.me/theorems/882814b4-dc52-45a9-a4df-d9a25d83bd7d
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  nnreal eq of smul haar 89aee63d41dc: P2 M Global Theory Companion Theory SW Pi Localization  nnreal eq of smul haar 89aee63d41dc
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  nnreal eq of smul haar 89aee63d41dc construction uses the P2 M Global Theory Companion Theory SW Pi Localization  nnreal eq of smul haar 89aee63d41dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankOneFiberMeasureBlockExtension.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankOneFiberMeasureBlockExtension.lean#L15-L26

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarModularCharacterOfContinuousAction
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RankOneFiberMeasureBlockExtension
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__nnreal_eq_of_smul_haar_89aee63d41dc {V : Type} [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    {c e : ℝ≥0} (h : c • μ = e • μ) : c = e := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«nnreal_eq_of_smul_haar» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__nnreal_eq_of_smul_haar_89aee63d41dc
