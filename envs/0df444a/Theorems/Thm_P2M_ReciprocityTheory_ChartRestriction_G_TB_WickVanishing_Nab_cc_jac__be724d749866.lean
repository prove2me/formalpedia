-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_jac__be724d749866
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_jac__be724d749866
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:18:00.015099+00:00
-- url     : https://prove2.me/theorems/ca6ea453-51e0-4d25-a625-11331df181a5
-- title:
--   P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab cc jac  be724d749866: P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab cc jac  be724d749866
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab cc jac  be724d749866 construction uses the P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab cc jac  be724d749866 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofComm.lean#L129-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofComm.lean#L129-L131

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)

theorem P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_jac__be724d749866 (c i : Fin d) : constantCoeff (Jac G c i) = if c = i then 1 else 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«TB».«WickVanishing».«Nab».«cc_jac'» := P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_jac__be724d749866
