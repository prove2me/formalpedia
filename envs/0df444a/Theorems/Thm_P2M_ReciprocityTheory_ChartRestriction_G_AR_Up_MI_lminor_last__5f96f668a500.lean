-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lminor_last__5f96f668a500
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lminor_last__5f96f668a500
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:03.408459+00:00
-- url     : https://prove2.me/theorems/75fd07cf-62c6-4d2a-abea-7e74e18ae699
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up MI lminor last  5f96f668a500: P2 M Reciprocity Theory Chart Restriction G AR Up MI lminor last  5f96f668a500
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up MI lminor last  5f96f668a500 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up MI lminor last  5f96f668a500 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfB.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfB.lean#L32-L33

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lminor_last__5f96f668a500 (M : Matrix (Fin n) (Fin n) ℂ) : lminor M (Fin.last n) = M.det := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«MI».«lminor_last'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lminor_last__5f96f668a500
