-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_WH_wt_add
-- name    : ReciprocityTheory.ChartRestriction.G.T0.WH.wt_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:26.24922+00:00
-- url     : https://prove2.me/theorems/8de58c5b-748b-449d-b3dc-b37999580a24
-- title:
--   WH: wt add
-- statement:
--   The WH construction uses the wt add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiPNeZero.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiPNeZero.lean#L11-L15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiPNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.WH
open MvPolynomial
variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] (p : σ → Prop) [DecidablePred p]

theorem ReciprocityTheory.ChartRestriction.G.T0.WH.wt_add (s t : σ →₀ ℕ) : wt p (s + t) = wt p s + wt p t := by sorry
