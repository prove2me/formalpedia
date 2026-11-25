-- Prove2me | Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_key
-- name    : PositivityTheory.CW.EigenspaceOrthogonality.key
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:49:48.100173+00:00
-- url     : https://prove2.me/theorems/185cfd61-b464-59d2-b352-a8dcd86d6009
-- title:
--   Eigenspace Orthogonality: key
-- statement:
--   The Eigenspace Orthogonality construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L68-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L68-L91

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

theorem PositivityTheory.CW.EigenspaceOrthogonality.key (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z))
    {c d : Fin n} (hcd : ε c = ε d) (x y : V) :
    beta ε E A (E c d x) y = beta ε E A x (E d c y) := by sorry
