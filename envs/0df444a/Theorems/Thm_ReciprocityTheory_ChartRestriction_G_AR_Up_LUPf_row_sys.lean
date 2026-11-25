-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_row_sys
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.row_sys
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:59:48.266151+00:00
-- url     : https://prove2.me/theorems/f54c150c-7970-529c-83cd-709bc482678b
-- title:
--   LUPf: row sys
-- statement:
--   The LUPf construction uses the row sys property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LUStatementPfA.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LUStatementPfA.lean#L59-L68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.row_sys (N M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hup : ∀ k : Fin n, i < k → N i k = 0) (hd : N i i = 1)
    (hz : ∀ j : Fin n, j < i → (N * M) i j = 0) :
    vecMul (fun k : Fin i => N i (Fin.castLE i.isLt.le k)) (lb M i) =
      -fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by sorry
