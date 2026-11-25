-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rootPoly_inter_mul_sdiff
-- name    : ReciprocityTheory.ChartRestriction.L1.rootPoly_inter_mul_sdiff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:36.605157+00:00
-- url     : https://prove2.me/theorems/7f2fff24-cb83-5533-9a1d-b5eb7df5d4d8
-- title:
--   L1: root Poly inter mul sdiff
-- statement:
--   The L1 construction uses the root Poly inter mul sdiff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedGcd.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedGcd.lean#L13-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedGcd
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

theorem ReciprocityTheory.ChartRestriction.L1.rootPoly_inter_mul_sdiff {E : Type} [Field E] (xs ys : Finset E) :
    rootPoly (xs ∩ ys) * rootPoly (xs \ ys) = rootPoly xs := by sorry
