-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rootPoly_isCoprime_of_disjoint
-- name    : ReciprocityTheory.ChartRestriction.L1.rootPoly_isCoprime_of_disjoint
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:48:23.374424+00:00
-- url     : https://prove2.me/theorems/71cde322-6163-4e31-838e-e963e6d0355c
-- title:
--   L1: root Poly is Coprime of disjoint
-- statement:
--   The L1 construction uses the root Poly is Coprime of disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedGcd.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedGcd.lean#L19-L25

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

theorem ReciprocityTheory.ChartRestriction.L1.rootPoly_isCoprime_of_disjoint {E : Type} [Field E] (xs ys : Finset E) (h : Disjoint xs ys) :
    IsCoprime (rootPoly xs) (rootPoly ys) := by sorry
