-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__vec_zero_2aa2babec28f
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__vec_zero_2aa2babec28f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:16.717787+00:00
-- url     : https://prove2.me/theorems/433aca99-ede8-4171-83ef-ee22aa9126b3
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  vec zero 2aa2babec28f: P2 M Global Theory Companion Theory SW Pi Localization  vec zero 2aa2babec28f
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  vec zero 2aa2babec28f construction uses the P2 M Global Theory Companion Theory SW Pi Localization  vec zero 2aa2babec28f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductScaling.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductScaling.lean#L51-L54

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductScaling
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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__vec_zero_2aa2babec28f {K : Type} [CommRing K] {M n : ℕ} (u : K) (c : Fin n → K) (X : Fin n → Fin M → K) :
    vec u c X 0 = u • (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → K) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«vec_zero» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__vec_zero_2aa2babec28f
