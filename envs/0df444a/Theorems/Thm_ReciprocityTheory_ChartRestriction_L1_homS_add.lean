-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_homS_add
-- name    : ReciprocityTheory.ChartRestriction.L1.homS_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:45:19.3989+00:00
-- url     : https://prove2.me/theorems/ff12763a-49f7-5ba2-9900-896ca3b36443
-- title:
--   L1: hom S add
-- statement:
--   The L1 construction uses the hom S add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedProjA.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedProjA.lean#L12-L13

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProjA
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
variable {K : Type} [Field K] (U : PowerSeries K)

theorem ReciprocityTheory.ChartRestriction.L1.homS_add (m : ℕ) (P Q : K[X]) : homS U m (P + Q) = homS U m P + homS U m Q := by sorry
