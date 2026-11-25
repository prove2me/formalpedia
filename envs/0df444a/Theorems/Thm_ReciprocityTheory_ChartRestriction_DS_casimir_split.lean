-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimir_split
-- name    : ReciprocityTheory.ChartRestriction.DS.casimir_split
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:38.316273+00:00
-- url     : https://prove2.me/theorems/003cb346-aa27-5b2a-8f9b-0dfc2aadc5da
-- title:
--   DS: casimir split
-- statement:
--   The DS construction uses the casimir split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/RhoEqRhoCAddRhoN.lean#L15-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/RhoEqRhoCAddRhoN.lean#L15-L60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.casimir_split {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    (P : Fin n → Fin n → Prop) [DecidableRel P] (hirr : ∀ a, ¬ P a a)
    (hP : ∀ a b, a ≠ b → (P a b ↔ ¬ P b a)) :
    casimir E = ∑ a, E a a * E a a +
      ∑ a, ∑ b ∈ univ.filter (fun b => P a b), (E a a - E b b + 2 • (E b a * E a b)) := by sorry
