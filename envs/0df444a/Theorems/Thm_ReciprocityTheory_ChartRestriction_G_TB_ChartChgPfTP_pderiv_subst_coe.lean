-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_pderiv_subst_coe
-- name    : ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst_coe
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:29.768156+00:00
-- url     : https://prove2.me/theorems/76e3a660-4569-58d3-8666-b93f0b115df5
-- title:
--   Chart Chg Pf TP: pderiv subst coe
-- statement:
--   The Chart Chg Pf TP construction uses the pderiv subst coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean#L97-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChgPfTP.lean#L97-L137

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

theorem ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst_coe {σ τ : Type} [Fintype σ] [DecidableEq σ] {a : σ → MvPowerSeries τ k} (hs : HasSubst a)
    (i : τ) (p : MvPolynomial σ k) :
    pderiv k i (substAlgHom hs (p : MvPowerSeries σ k)) =
      ∑ s, substAlgHom hs (pderiv k s (p : MvPowerSeries σ k)) * pderiv k i (a s) := by sorry
