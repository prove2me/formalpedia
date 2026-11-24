-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rootPoly_eval
-- name    : ReciprocityTheory.ChartRestriction.L1.rootPoly_eval
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:55:09.478043+00:00
-- url     : https://prove2.me/theorems/16a966ad-7acb-4994-9021-eae70548e02b
-- title:
--   L1: root Poly eval
-- statement:
--   The L1 construction uses the root Poly eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluAlg.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluAlg.lean#L21-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluAlg
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
variable {K : Type} [Field K] [CharZero K] [DecidableEq K] (g2 g3 : K) (xs : Finset K)

theorem ReciprocityTheory.ChartRestriction.L1.rootPoly_eval (t : K) : (rootPoly xs).eval t = ∏ x ∈ xs, (t - x) := by sorry
