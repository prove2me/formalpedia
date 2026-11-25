-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__pi_const_smul_94c0c5ccccb8
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__pi_const_smul_94c0c5ccccb8
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:31.2917+00:00
-- url     : https://prove2.me/theorems/f72170b0-0012-43e9-a01e-ff104f708aaa
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  pi const smul 94c0c5ccccb8: P2 M Global Theory Companion Theory SW Pi Localization  pi const smul 94c0c5ccccb8
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  pi const smul 94c0c5ccccb8 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  pi const smul 94c0c5ccccb8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasureConsProduct.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasureConsProduct.lean#L14-L23

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureConsProduct
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
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__pi_const_smul_94c0c5ccccb8 {ι X : Type} [Fintype ι] [MeasurableSpace X] (κ : Measure X) [SigmaFinite κ] (c : ℝ≥0) :
    Measure.pi (fun _ : ι => c • κ) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => κ) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«pi_const_smul» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__pi_const_smul_94c0c5ccccb8
