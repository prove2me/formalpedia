-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rootPoly_eval_mem
-- name    : ReciprocityTheory.ChartRestriction.L1.rootPoly_eval_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:49.067802+00:00
-- url     : https://prove2.me/theorems/c7ac2c06-195d-5e84-b437-c7b7a61446da
-- title:
--   L1: root Poly eval mem
-- statement:
--   The L1 construction uses the root Poly eval mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluAlg.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluAlg.lean#L32-L34

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

theorem ReciprocityTheory.ChartRestriction.L1.rootPoly_eval_mem {t : K} (ht : t ∈ xs) : (rootPoly xs).eval t = 0 := by sorry
