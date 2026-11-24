-- Prove2me | Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_MR_mul
-- name    : PositivityTheory.CW.GradedNormalNilpotent.MR_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:05.24316+00:00
-- url     : https://prove2.me/theorems/c26d528f-ec66-45be-8e95-e3663f2cf7d8
-- title:
--   Graded Normal Nilpotent: MR mul
-- statement:
--   The Graded Normal Nilpotent construction uses the MR mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L192-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L192-L200

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CommutatorAdjointHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS Polynomial
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.GradedNormalNilpotent
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
variable {ε E}
variable (h : Hyp ε E)

theorem PositivityTheory.CW.GradedNormalNilpotent.MR_mul (M M' : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (i j : ℕ) (hM : ∀ a b, M a b ∈ U E i)
    (hM' : ∀ a b, M' a b ∈ U E j) :
    ∃ h'' : ∀ a b, (M * M') a b ∈ U E (i + j), MR h M i hM * MR h M' j hM' = MR h (M * M') (i + j) h'' := by sorry
