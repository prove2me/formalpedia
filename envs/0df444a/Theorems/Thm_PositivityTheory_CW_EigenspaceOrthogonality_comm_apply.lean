-- Prove2me | Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_comm_apply
-- name    : PositivityTheory.CW.EigenspaceOrthogonality.comm_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:50:03.39596+00:00
-- url     : https://prove2.me/theorems/f934205f-73ba-4b1d-9be9-e464dcd32f14
-- title:
--   Eigenspace Orthogonality: comm apply
-- statement:
--   The Eigenspace Orthogonality construction uses the comm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L41-L47

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

theorem PositivityTheory.CW.EigenspaceOrthogonality.comm_apply (hgl : IsGlRep E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) +
      ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by sorry
