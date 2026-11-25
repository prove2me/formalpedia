-- Prove2me | Theorems.Thm_P2M_GlobalTheory_JR_LatTop_isLocallyConstant_indicator_one__9454ef2e65f5
-- name    : P2M_GlobalTheory_JR_LatTop_isLocallyConstant_indicator_one__9454ef2e65f5
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:05.153135+00:00
-- url     : https://prove2.me/theorems/3951b4aa-ba0d-4f4f-810a-56386a1d860f
-- title:
--   P2 M Global Theory JR Lat Top is Locally Constant indicator one  9454ef2e65f5: P2 M Global Theory JR Lat Top is Locally Constant indicator one  9454ef2e65f5
-- statement:
--   The P2 M Global Theory JR Lat Top is Locally Constant indicator one  9454ef2e65f5 construction uses the P2 M Global Theory JR Lat Top is Locally Constant indicator one  9454ef2e65f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianLatticeIsOpenIsCompactTest.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianLatticeIsOpenIsCompactTest.lean#L7-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianLatticeIsOpenIsCompactTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LatTop

theorem P2M_GlobalTheory_JR_LatTop_isLocallyConstant_indicator_one__9454ef2e65f5 {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by sorry

alias «GlobalTheory».«JR».«LatTop».«isLocallyConstant_indicator_one'» := P2M_GlobalTheory_JR_LatTop_isLocallyConstant_indicator_one__9454ef2e65f5
