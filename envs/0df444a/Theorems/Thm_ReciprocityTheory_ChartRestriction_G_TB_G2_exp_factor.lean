-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_exp_factor
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.exp_factor
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:44.937632+00:00
-- url     : https://prove2.me/theorems/cf9bf8f4-d766-4980-9b66-f1e2ab75bb7c
-- title:
--   G2: exp factor
-- statement:
--   The G2 construction uses the exp factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/KillAdd.lean#L12-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/KillAdd.lean#L12-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateEqTG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAdd
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.exp_factor {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type} (f : MvPowerSeries σ k)
    (hf : constantCoeff f = 0) :
    ∃ Y : MvPowerSeries σ k, PowerSeries.subst f (PowerSeries.exp k) = 1 + f * Y := by sorry
