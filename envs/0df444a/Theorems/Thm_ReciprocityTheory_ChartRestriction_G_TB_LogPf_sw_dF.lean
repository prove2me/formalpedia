-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_sw_dF
-- name    : ReciprocityTheory.ChartRestriction.G.TB.LogPf.sw_dF
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:32.374324+00:00
-- url     : https://prove2.me/theorems/a24194ba-e4f0-5be1-bab3-acfe3880730a
-- title:
--   Log Pf: sw d F
-- statement:
--   The Log Pf construction uses the sw d F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogClosed.lean#L169-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogClosed.lean#L169-L176

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)

theorem ReciprocityTheory.ChartRestriction.G.TB.LogPf.sw_dF (j b : Fin d) :
    ev (n := 2) ![pt k d 1, pt k d 0] (pderiv k ((1 : Fin 2), b) (G.F j)) = pderiv k ((0 : Fin 2), b) (G.F j) := by sorry
