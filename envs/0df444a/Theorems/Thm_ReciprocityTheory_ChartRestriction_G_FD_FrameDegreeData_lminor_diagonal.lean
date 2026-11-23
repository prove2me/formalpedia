-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_lminor_diagonal
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_diagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:11.177807+00:00
-- url     : https://prove2.me/theorems/4dcb23af-7aec-424c-b3c9-711987a95aaa
-- title:
--   Frame Degree Data: lminor diagonal
-- statement:
--   The Frame Degree Data construction uses the lminor diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ProdCastLESucc.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ProdCastLESucc.lean#L28-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_diagonal (D : Fin n → ℂ) (i : Fin (n + 1)) :
    lminor (Matrix.diagonal D) i = ∏ j : Fin i, D (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by sorry
