-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WirtChain_contDiffOn_wirtWord__3aa88b37ccd1
-- name    : P2M_GlobalTheory_WirtChain_contDiffOn_wirtWord__3aa88b37ccd1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:50.781021+00:00
-- url     : https://prove2.me/theorems/b408e411-73e8-4a9e-8e8b-0d1fd9c2a1dc
-- title:
--   P2 M Global Theory Wirt Chain cont Diff On wirt Word  3aa88b37ccd1: P2 M Global Theory Wirt Chain cont Diff On wirt Word  3aa88b37ccd1
-- statement:
--   The P2 M Global Theory Wirt Chain cont Diff On wirt Word  3aa88b37ccd1 construction uses the P2 M Global Theory Wirt Chain cont Diff On wirt Word  3aa88b37ccd1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean#L19-L23

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

theorem P2M_GlobalTheory_WirtChain_contDiffOn_wirtWord__3aa88b37ccd1 {V : Set (Φ → ℂ)} (hV : IsOpen V) {g : (Φ → ℂ) → ℂ} (hg : ContDiffOn ℝ ∞ g V)
    (w : List (Φ × Bool)) : ContDiffOn ℝ ∞ (wirtWord w g) V := by sorry

alias «GlobalTheory».«WirtChain».«contDiffOn_wirtWord'» := P2M_GlobalTheory_WirtChain_contDiffOn_wirtWord__3aa88b37ccd1
