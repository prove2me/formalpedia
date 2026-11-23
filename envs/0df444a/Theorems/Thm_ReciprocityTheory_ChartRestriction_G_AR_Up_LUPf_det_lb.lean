-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_det_lb
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.det_lb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:22.254738+00:00
-- url     : https://prove2.me/theorems/4af9643a-000d-49e5-bd96-747a8aee75b7
-- title:
--   LUPf: det lb
-- statement:
--   The LUPf construction uses the det lb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LUStatementPfA.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LUStatementPfA.lean#L15-L16

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.det_lb (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (lb M i).det = lminor M (Fin.castSucc i) := by sorry
