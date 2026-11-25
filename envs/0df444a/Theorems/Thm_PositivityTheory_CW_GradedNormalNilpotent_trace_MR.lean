-- Prove2me | Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_trace_MR
-- name    : PositivityTheory.CW.GradedNormalNilpotent.trace_MR
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:22.292339+00:00
-- url     : https://prove2.me/theorems/a0c4e964-0f3d-5067-92d3-34f62e9fe420
-- title:
--   Graded Normal Nilpotent: trace MR
-- statement:
--   The Graded Normal Nilpotent construction uses the trace MR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L235-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L235-L241

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

theorem PositivityTheory.CW.GradedNormalNilpotent.trace_MR (M : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (j : ℕ) (hM : ∀ a b, M a b ∈ U E j)
    (hT : M.trace ∈ U E j) : ((psi h).mapMatrix (MR h M j hM)).trace = psi h (L h j M.trace hT) := by sorry
