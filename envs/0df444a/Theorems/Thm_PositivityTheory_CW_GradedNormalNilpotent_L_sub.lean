-- Prove2me | Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_L_sub
-- name    : PositivityTheory.CW.GradedNormalNilpotent.L_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:23.570024+00:00
-- url     : https://prove2.me/theorems/f0be44e2-7141-46ed-ba24-7faa3896962e
-- title:
--   Graded Normal Nilpotent: L sub
-- statement:
--   The Graded Normal Nilpotent construction uses the L sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L231-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L231-L233

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

theorem PositivityTheory.CW.GradedNormalNilpotent.L_sub (j : ℕ) (x y : Module.End ℂ V) (hx : x ∈ U E j) (hy : y ∈ U E j) :
    L h j x hx - L h j y hy = L h j (x - y) (sub_mem hx hy) := by sorry
