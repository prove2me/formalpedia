-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_zp
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.zp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:43:24.243967+00:00
-- url     : https://prove2.me/theorems/2fe4f520-7e27-5ffd-a8d5-44241419cc15
-- title:
--   Nab: zp
-- statement:
--   The Nab construction uses the zp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ConstantCoeffAddFirstSecond.lean#L22-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ConstantCoeffAddFirstSecond.lean#L22-L39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyPointZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffAddFirstSecond
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
variable {k : Type} [CommRing k] {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.zp (h : PS k 2 d) (i : Fin d) (p : Pt k 3 d) (hp : ∀ c, constantCoeff (p c) = 0)
    (hpz : ∀ c, pderiv k ((2 : Fin 3), i) (p c) = 0) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), i) (ev (n := 3) ![p, pt k d 2] h)) =
      -ev (n := 2) ![fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (p c)]
        (-ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) h)) := by sorry
