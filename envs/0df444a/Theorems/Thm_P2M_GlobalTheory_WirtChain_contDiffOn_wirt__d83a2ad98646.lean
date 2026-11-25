-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WirtChain_contDiffOn_wirt__d83a2ad98646
-- name    : P2M_GlobalTheory_WirtChain_contDiffOn_wirt__d83a2ad98646
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:12:10.145619+00:00
-- url     : https://prove2.me/theorems/489b13b1-f86e-4c37-b367-cf23b321ab50
-- title:
--   P2 M Global Theory Wirt Chain cont Diff On wirt  d83a2ad98646: P2 M Global Theory Wirt Chain cont Diff On wirt  d83a2ad98646
-- statement:
--   The P2 M Global Theory Wirt Chain cont Diff On wirt  d83a2ad98646 construction uses the P2 M Global Theory Wirt Chain cont Diff On wirt  d83a2ad98646 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L13-L17

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

theorem P2M_GlobalTheory_WirtChain_contDiffOn_wirt__d83a2ad98646 {V : Set (Φ → ℂ)} (hV : IsOpen V) {g : (Φ → ℂ) → ℂ} (hg : ContDiffOn ℝ ∞ g V)
    (τ : Φ) (bar : Bool) : ContDiffOn ℝ ∞ (wirt τ bar g) V := by sorry

alias «GlobalTheory».«WirtChain».«contDiffOn_wirt'» := P2M_GlobalTheory_WirtChain_contDiffOn_wirt__d83a2ad98646
