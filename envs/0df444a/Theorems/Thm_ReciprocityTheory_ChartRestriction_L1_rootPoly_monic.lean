-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rootPoly_monic
-- name    : ReciprocityTheory.ChartRestriction.L1.rootPoly_monic
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:55:19.384456+00:00
-- url     : https://prove2.me/theorems/8895a7c4-0caa-462d-82fb-c2a0254eba96
-- title:
--   L1: root Poly monic
-- statement:
--   The L1 construction uses the root Poly monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluAlg.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluAlg.lean#L12-L14

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

theorem ReciprocityTheory.ChartRestriction.L1.rootPoly_monic : (rootPoly xs).Monic := by sorry
