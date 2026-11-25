-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_veluNum_eval
-- name    : ReciprocityTheory.ChartRestriction.L1.veluNum_eval
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:51.445432+00:00
-- url     : https://prove2.me/theorems/f651f234-1549-5fd9-ac99-505b82a4e112
-- title:
--   L1: velu Num eval
-- statement:
--   The L1 construction uses the velu Num eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluAlg.lean#L47-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluAlg.lean#L47-L60

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

theorem ReciprocityTheory.ChartRestriction.L1.veluNum_eval {t : K} (ht : t ∉ xs) :
    (veluNum g2 g3 xs).eval t = veluFun g2 g3 xs t * (rootPoly xs).eval t ^ 2 := by sorry
