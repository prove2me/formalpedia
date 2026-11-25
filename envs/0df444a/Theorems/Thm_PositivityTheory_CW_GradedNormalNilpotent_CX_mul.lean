-- Prove2me | Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_CX_mul
-- name    : PositivityTheory.CW.GradedNormalNilpotent.CX_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:36.651349+00:00
-- url     : https://prove2.me/theorems/0a63b85b-c13c-5d19-a9ae-0c1150a1815a
-- title:
--   Graded Normal Nilpotent: CX mul
-- statement:
--   The Graded Normal Nilpotent construction uses the CX mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L186-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L186-L190

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

theorem PositivityTheory.CW.GradedNormalNilpotent.CX_mul (x y : Module.End ℂ V) (i j : ℕ) :
    (C x * X ^ i) * (C y * X ^ j) = C (x * y) * X ^ (i + j) := by sorry
