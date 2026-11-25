-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_range_fin_append
-- name    : ReciprocityTheory.MultiplicativeHeights.DegAdd.range_fin_append
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:01:42.617139+00:00
-- url     : https://prove2.me/theorems/26fd82bc-b4e0-4f65-8d83-5c697cdb9fa8
-- title:
--   Deg Add: range fin append
-- statement:
--   The Deg Add construction uses the range fin append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsIntSmulMemSpan.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsIntSmulMemSpan.lean#L49-L59

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Lemmata_GeneralBFactBisAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DegAdd
open NumberField

theorem ReciprocityTheory.MultiplicativeHeights.DegAdd.range_fin_append {α : Type} {k m : ℕ} (b : Fin k → α) (c : Fin m → α) :
    Set.range (Fin.append b c) = Set.range b ∪ Set.range c := by sorry
