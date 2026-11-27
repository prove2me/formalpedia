-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_casimirK_add
-- name    : ReciprocityTheory.ChartRestriction.DS.BigCasimir.casimirK_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:51.672898+00:00
-- url     : https://prove2.me/theorems/a5d3d84d-bbaf-42f9-af63-0c066e10b051
-- title:
--   Big Casimir: casimir K add
-- statement:
--   The Big Casimir construction uses the casimir K add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCasA.lean#L41-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCasA.lean#L41-L52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.BigCasimir
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}

theorem ReciprocityTheory.ChartRestriction.DS.BigCasimir.casimirK_add (A B : Fin n → Fin n → Module.End ℂ X)
    (hAB : ∀ a b c d, A a b * B c d = B c d * A a b) :
    casimirK ε (A + B) = casimirK ε A + casimirK ε B +
      2 • ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), B a b * A b a := by sorry
