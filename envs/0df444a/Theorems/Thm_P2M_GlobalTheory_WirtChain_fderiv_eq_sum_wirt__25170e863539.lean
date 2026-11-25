-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WirtChain_fderiv_eq_sum_wirt__25170e863539
-- name    : P2M_GlobalTheory_WirtChain_fderiv_eq_sum_wirt__25170e863539
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:06.845138+00:00
-- url     : https://prove2.me/theorems/88996aa9-cc6a-4ac1-b6bc-8f5b5abcdca1
-- title:
--   P2 M Global Theory Wirt Chain fderiv eq sum wirt  25170e863539: P2 M Global Theory Wirt Chain fderiv eq sum wirt  25170e863539
-- statement:
--   The P2 M Global Theory Wirt Chain fderiv eq sum wirt  25170e863539 construction uses the P2 M Global Theory Wirt Chain fderiv eq sum wirt  25170e863539 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L26-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L26-L51

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnWirtWordMulExpComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.WirtChain
open Complex
variable {Φ I : Type} [Fintype Φ] [Fintype I]
open Classical

theorem P2M_GlobalTheory_WirtChain_fderiv_eq_sum_wirt__25170e863539 (h : (Φ → ℂ) → ℂ) (y u : Φ → ℂ) :
    fderiv ℝ h y u = ∑ τ, (u τ * wirt τ false h y + (starRingEnd ℂ) (u τ) * wirt τ true h y) := by sorry

alias «GlobalTheory».«WirtChain».«fderiv_eq_sum_wirt'» := P2M_GlobalTheory_WirtChain_fderiv_eq_sum_wirt__25170e863539
