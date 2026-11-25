-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_valDiv2_even_of_pows
-- name    : ReciprocityTheory.ChartRestriction.L1.valDiv2_even_of_pows
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:08:30.155888+00:00
-- url     : https://prove2.me/theorems/0226ecef-11ad-5402-931f-74251d329b7b
-- title:
--   L1: val Div2 even of pows
-- statement:
--   The L1 construction uses the val Div2 even of pows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/Norm1728EqOneOfFiveLe.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/Norm1728EqOneOfFiveLe.lean#L13-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKurOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_Norm1728EqOneOfFiveLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.valDiv2_even_of_pows {l t : ℝ} (hl : 1 < l) {a b : ℤ} {n : ℕ} (hn : ¬ 2 ∣ n)
    (h4 : t ^ 4 = l ^ b) (h1 : t ^ (2 * n) * l ^ a = 1) : ∃ m : ℤ, b = 2 * m := by sorry
