-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_vf_sum
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.vf_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:40.154297+00:00
-- url     : https://prove2.me/theorems/c8ef4680-be31-463f-bb8a-39ed62df205a
-- title:
--   Nab: vf sum
-- statement:
--   The Nab construction uses the vf sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ConnectionKillsSeries.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ConnectionKillsSeries.lean#L24-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionKillsSeries
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {k : Type} [CommRing k] {τ : Type} [Fintype τ]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.vf_sum {ι : Type} (s : Finset ι) (c : τ → MvPowerSeries τ k) (f : ι → MvPowerSeries τ k) :
    vf c (∑ i ∈ s, f i) = ∑ i ∈ s, vf c (f i) := by sorry
