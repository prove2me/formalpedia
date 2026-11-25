-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_pderiv_subst
-- name    : ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:15.615122+00:00
-- url     : https://prove2.me/theorems/4e6d0b18-c964-5f20-8b4d-1b0bde212039
-- title:
--   Chart Chg Pf TP: pderiv subst
-- statement:
--   The Chart Chg Pf TP construction uses the pderiv subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean#L139-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean#L139-L183

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChgPfTP
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
variable {k : Type} [CommRing k]

theorem ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst {σ τ : Type} [Fintype σ] [DecidableEq σ] (a : σ → MvPowerSeries τ k)
    (ha : ∀ s, constantCoeff (a s) = 0) (i : τ) (f : MvPowerSeries σ k) :
    pderiv k i (subst a f) = ∑ s, subst a (pderiv k s f) * pderiv k i (a s) := by sorry
