-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rootPoly_eval_ne
-- name    : ReciprocityTheory.ChartRestriction.L1.rootPoly_eval_ne
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:49:05.642186+00:00
-- url     : https://prove2.me/theorems/46cb3914-804b-5778-94b1-e8e79ef6f8e3
-- title:
--   L1: root Poly eval ne
-- statement:
--   The L1 construction uses the root Poly eval ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluAlg.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluAlg.lean#L26-L30

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

theorem ReciprocityTheory.ChartRestriction.L1.rootPoly_eval_ne {t : K} (ht : t ∉ xs) : (rootPoly xs).eval t ≠ 0 := by sorry
