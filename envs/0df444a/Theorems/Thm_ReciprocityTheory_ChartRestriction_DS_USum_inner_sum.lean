-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_inner_sum
-- name    : ReciprocityTheory.ChartRestriction.DS.USum.inner_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:16:23.643961+00:00
-- url     : https://prove2.me/theorems/035993d8-d78d-44d3-bece-7a3558b06193
-- title:
--   USum: inner sum
-- statement:
--   The USum construction uses the inner sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L46-L47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix WithLp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.USum
variable {n : ℕ}
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

theorem ReciprocityTheory.ChartRestriction.DS.USum.inner_sum (x y : WithLp 2 (H₁ × H₂)) :
    inner ℂ x y = inner ℂ (ofLp x).1 (ofLp y).1 + inner ℂ (ofLp x).2 (ofLp y).2 := by sorry
