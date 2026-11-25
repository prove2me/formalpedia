-- Prove2me | Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_psiL_iff
-- name    : PositivityTheory.CW.GradedNormalNilpotent.psiL_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:50.436995+00:00
-- url     : https://prove2.me/theorems/9f01c317-fdcc-4c94-a11b-a960dea5f3aa
-- title:
--   Graded Normal Nilpotent: psi L iff
-- statement:
--   The Graded Normal Nilpotent construction uses the psi L iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L219-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L219-L229

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

theorem PositivityTheory.CW.GradedNormalNilpotent.psiL_iff (j : ℕ) (x : Module.End ℂ V) (hx : x ∈ U E j) : psi h (L h j x hx) = 0 ↔ x ∈ Jk ε E j := by sorry
