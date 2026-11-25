-- Prove2me | Theorems.Thm_P2M_GlobalTheory_JR_HeightSquareIntegrable_tsum_pi_prod_le__f38cf3f9f8ef
-- name    : P2M_GlobalTheory_JR_HeightSquareIntegrable_tsum_pi_prod_le__f38cf3f9f8ef
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:48.198805+00:00
-- url     : https://prove2.me/theorems/7f00aa93-e383-4243-ad39-8672ae618cf3
-- title:
--   P2 M Global Theory JR Height Square Integrable tsum pi prod le  f38cf3f9f8ef: P2 M Global Theory JR Height Square Integrable tsum pi prod le  f38cf3f9f8ef
-- statement:
--   The P2 M Global Theory JR Height Square Integrable tsum pi prod le  f38cf3f9f8ef construction uses the P2 M Global Theory JR Height Square Integrable tsum pi prod le  f38cf3f9f8ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHeightSqLintegralLtTop.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHeightSqLintegralLtTop.lean#L14-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegralityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHeightSqLintegralLtTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HeightSquareIntegrable

theorem P2M_GlobalTheory_JR_HeightSquareIntegrable_tsum_pi_prod_le__f38cf3f9f8ef {ι : Type} [Fintype ι] {α : ι → Type} (f : ∀ i, α i → ℝ≥0∞) :
    ∑' t : ∀ i, α i, ∏ i, f i (t i) ≤ ∏ i, ∑' x, f i x := by sorry

alias «GlobalTheory».«JR».«HeightSquareIntegrable».«tsum_pi_prod_le'» := P2M_GlobalTheory_JR_HeightSquareIntegrable_tsum_pi_prod_le__f38cf3f9f8ef
