-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lu_unique
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.MI.lu_unique
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:58.830262+00:00
-- url     : https://prove2.me/theorems/701bdef2-c2dd-5f09-befd-2b75ad86d6a9
-- title:
--   MI: lu unique
-- statement:
--   The MI construction uses the lu unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfB.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfB.lean#L25-L30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_Lemmata_GeneralBFactForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.MI.lu_unique {N N' U U' : Matrix (Fin n) (Fin n) ℂ}
    (hN : N.BlockTriangular OrderDual.toDual) (hN1 : ∀ a, N a a = 1)
    (hN' : N'.BlockTriangular OrderDual.toDual) (hN'1 : ∀ a, N' a a = 1)
    (hU : U.BlockTriangular id) (hU' : U'.BlockTriangular id) (hd : U'.det ≠ 0)
    (h : N * U = N' * U') : N = N' ∧ U = U' := by sorry
