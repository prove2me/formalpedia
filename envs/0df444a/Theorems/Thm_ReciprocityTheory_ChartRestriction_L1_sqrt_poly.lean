-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_sqrt_poly
-- name    : ReciprocityTheory.ChartRestriction.L1.sqrt_poly
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:07:00.363083+00:00
-- url     : https://prove2.me/theorems/b4d23a5d-f1a7-5f36-8fdd-828814417c32
-- title:
--   L1: sqrt poly
-- statement:
--   The L1 construction uses the sqrt poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedSqrt.lean#L10-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedSqrt.lean#L10-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedSqrt
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

theorem ReciprocityTheory.ChartRestriction.L1.sqrt_poly {E : Type} [Field E] [CharZero E] (k : Subfield E) (h : E[X]) (hm : h.Monic)
    (hk : ∀ i, (h ^ 2).coeff i ∈ k) : ∀ i, h.coeff i ∈ k := by sorry
