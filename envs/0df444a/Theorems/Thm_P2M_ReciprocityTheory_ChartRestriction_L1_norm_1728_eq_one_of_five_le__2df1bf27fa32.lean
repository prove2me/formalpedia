-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_norm_1728_eq_one_of_five_le__2df1bf27fa32
-- name    : P2M_ReciprocityTheory_ChartRestriction_L1_norm_1728_eq_one_of_five_le__2df1bf27fa32
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:07:56.239668+00:00
-- url     : https://prove2.me/theorems/b597c245-1bdc-5598-ab75-03a86d590d3b
-- title:
--   P2 M Reciprocity Theory Chart Restriction L1 norm 1728 eq one of five le  2df1bf27fa32: P2 M Reciprocity Theory Chart Restriction L1 norm 1728 eq one of five le  2df1bf27fa32
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction L1 norm 1728 eq one of five le  2df1bf27fa32 construction uses the P2 M Reciprocity Theory Chart Restriction L1 norm 1728 eq one of five le  2df1bf27fa32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormWeierstrassCoeffSmallJ.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormWeierstrassCoeffSmallJ.lean#L59-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKurOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_G2EqZeroOfHasCMByThree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormWeierstrassCoeffSmallJ
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
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable (l : ℕ) [Fact l.Prime]

theorem P2M_ReciprocityTheory_ChartRestriction_L1_norm_1728_eq_one_of_five_le__2df1bf27fa32 (h5 : 5 ≤ l) : ‖(1728 : ℂ_[l])‖ = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«L1».«norm_1728_eq_one_of_five_le'» := P2M_ReciprocityTheory_ChartRestriction_L1_norm_1728_eq_one_of_five_le__2df1bf27fa32
