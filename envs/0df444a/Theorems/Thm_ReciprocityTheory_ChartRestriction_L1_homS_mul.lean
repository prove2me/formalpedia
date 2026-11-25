-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_homS_mul
-- name    : ReciprocityTheory.ChartRestriction.L1.homS_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:45:39.951646+00:00
-- url     : https://prove2.me/theorems/76260b19-e474-4567-ab4a-629ce03530cb
-- title:
--   L1: hom S mul
-- statement:
--   The L1 construction uses the hom S mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedProjA.lean#L38-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedProjA.lean#L38-L61

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

theorem ReciprocityTheory.ChartRestriction.L1.homS_mul (m n : ℕ) (P Q : K[X]) (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) :
    homS U (m + n) (P * Q) = homS U m P * homS U n Q := by sorry
