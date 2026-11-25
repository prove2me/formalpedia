-- Prove2me | Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_MR_pow
-- name    : PositivityTheory.CW.GradedNormalNilpotent.MR_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:49:55.211869+00:00
-- url     : https://prove2.me/theorems/77bc647f-c501-56be-9b94-ddae449eb4fc
-- title:
--   Graded Normal Nilpotent: MR pow
-- statement:
--   The Graded Normal Nilpotent construction uses the MR pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L202-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L202-L215

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

theorem PositivityTheory.CW.GradedNormalNilpotent.MR_pow (M : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (j : ℕ) (hM : ∀ a b, M a b ∈ U E j) (k : ℕ) :
    ∃ hk : ∀ a b, (M ^ (k + 1)) a b ∈ U E (j * (k + 1)), MR h M j hM ^ (k + 1) = MR h (M ^ (k + 1)) (j * (k + 1)) hk := by sorry
