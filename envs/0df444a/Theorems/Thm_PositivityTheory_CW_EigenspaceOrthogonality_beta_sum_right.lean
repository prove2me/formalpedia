-- Prove2me | Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_beta_sum_right
-- name    : PositivityTheory.CW.EigenspaceOrthogonality.beta_sum_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:50:10.53447+00:00
-- url     : https://prove2.me/theorems/39c6750c-0973-4af7-be25-f708b3b26f3b
-- title:
--   Eigenspace Orthogonality: beta sum right
-- statement:
--   The Eigenspace Orthogonality construction uses the beta sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L98-L101

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

theorem PositivityTheory.CW.EigenspaceOrthogonality.beta_sum_right {ι : Type*} (s : Finset ι) (f : ι → V) (v : V) :
    beta ε E A v (∑ i ∈ s, f i) = ∑ i ∈ s, beta ε E A v (f i) := by sorry
