-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isDerivedOn_trivial
-- name    : ReciprocityTheory.ChartRestriction.DS.isDerivedOn_trivial
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:29.074617+00:00
-- url     : https://prove2.me/theorems/a9f2ebe3-d0ea-4c68-a9a1-acc3a553080c
-- title:
--   DS: is Derived On trivial
-- statement:
--   The DS construction uses the is Derived On trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L9-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L9-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.isDerivedOn_trivial {n : ℕ} (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] :
    IsURepOn (UJset ε) (fun _ : Matrix (Fin n) (Fin n) ℂ => (1 : H →L[ℂ] H)) ∧
      IsDerivedOn ε (fun _ : Matrix (Fin n) (Fin n) ℂ => (1 : H →L[ℂ] H)) ⊤ (fun _ _ => 0) := by sorry
