-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_T_eq
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.T_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:53.464063+00:00
-- url     : https://prove2.me/theorems/0fec65d5-faa2-4eb2-88ac-074a3b4e78c4
-- title:
--   Nab: T eq
-- statement:
--   The Nab construction uses the T eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofComm.lean#L169-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofComm.lean#L169-L181

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.T_eq (b i j : Fin d) :
    ∑ c, Jac G c b * pderiv k ((0 : Fin 1), c) (Jac G j i) =
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (Ar G j i)) +
      ∑ c, Jac G j c * C (constantCoeff (pderiv k ((0 : Fin 1), b) (Jac G c i))) := by sorry
