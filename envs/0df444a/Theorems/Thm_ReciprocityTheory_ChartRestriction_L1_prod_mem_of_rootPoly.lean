-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_prod_mem_of_rootPoly
-- name    : ReciprocityTheory.ChartRestriction.L1.prod_mem_of_rootPoly
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:18:48.631287+00:00
-- url     : https://prove2.me/theorems/41859dfe-0379-46df-81cf-514a1866a290
-- title:
--   L1: prod mem of root Poly
-- statement:
--   The L1 construction uses the prod mem of root Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerPoly.lean#L33-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerPoly.lean#L33-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedSqrt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerPoly
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
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.prod_mem_of_rootPoly {E : Type} [Field E] (k : Subfield E) (xs : Finset E)
    (h : ∀ i, (rootPoly xs).coeff i ∈ k) : ∏ x ∈ xs, x ∈ k := by sorry
