-- Prove2me | Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_s1
-- name    : PositivityTheory.CW.EigenspaceOrthogonality.s1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:50:04.699932+00:00
-- url     : https://prove2.me/theorems/fa7d14fb-2b1c-5c57-a886-366ef277e6a2
-- title:
--   Eigenspace Orthogonality: s1
-- statement:
--   The Eigenspace Orthogonality construction uses the s1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L19-L28

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigenspacesOrthogonalOfCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.EigenspaceOrthogonality
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {A : Module.End ℂ V}

theorem PositivityTheory.CW.EigenspaceOrthogonality.s1 (g : Fin n → Fin n → ℂ) (c : Fin n) :
    (∑ a, ∑ b, if ε a ≠ ε b then (if c = a then g a b else 0) else 0) =
      ∑ b, if ε c ≠ ε b then g c b else 0 := by sorry
