-- Prove2me | Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_s2
-- name    : PositivityTheory.CW.EigenspaceOrthogonality.s2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:50:03.480381+00:00
-- url     : https://prove2.me/theorems/f01bc488-556e-5d28-aa37-1014698adf37
-- title:
--   Eigenspace Orthogonality: s2
-- statement:
--   The Eigenspace Orthogonality construction uses the s2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L30-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L30-L39

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

theorem PositivityTheory.CW.EigenspaceOrthogonality.s2 (g : Fin n → Fin n → ℂ) (d : Fin n) :
    (∑ a, ∑ b, if ε a ≠ ε b then (if b = d then g a b else 0) else 0) =
      ∑ a, if ε a ≠ ε d then g a d else 0 := by sorry
