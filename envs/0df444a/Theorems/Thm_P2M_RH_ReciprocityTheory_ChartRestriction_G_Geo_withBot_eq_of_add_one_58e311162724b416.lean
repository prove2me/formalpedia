-- Prove2me | Theorems.Thm_P2M_RH_ReciprocityTheory_ChartRestriction_G_Geo_withBot_eq_of_add_one_58e311162724b416
-- name    : P2M_RH_ReciprocityTheory_ChartRestriction_G_Geo_withBot_eq_of_add_one_58e311162724b416
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:06.039305+00:00
-- url     : https://prove2.me/theorems/6906c087-2e77-47d7-b99d-c9759a477a78
-- title:
--   P2 M RH Reciprocity Theory Chart Restriction G Geo with Bot eq of add one 58e311162724b416: P2 M RH Reciprocity Theory Chart Restriction G Geo with Bot eq of add one 58e311162724b416
-- statement:
--   The P2 M RH Reciprocity Theory Chart Restriction G Geo with Bot eq of add one 58e311162724b416 construction uses the P2 M RH Reciprocity Theory Chart Restriction G Geo with Bot eq of add one 58e311162724b416 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean#L40-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppA
import Definitions.Def_Lemmata_GeneralBFactTerForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {σ : Type*} [Finite σ]

theorem P2M_RH_ReciprocityTheory_ChartRestriction_G_Geo_withBot_eq_of_add_one_58e311162724b416 {x : WithBot ℕ∞} {m : ℕ} (h : x + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) :
    x = (m : WithBot ℕ∞) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«withBot_eq_of_add_one» := P2M_RH_ReciprocityTheory_ChartRestriction_G_Geo_withBot_eq_of_add_one_58e311162724b416
