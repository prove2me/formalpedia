-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_perm_inr
-- name    : ReciprocityTheory.ChartRestriction.G.TB.SCPf.perm_inr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:42:39.626003+00:00
-- url     : https://prove2.me/theorems/5c68d881-1e99-43c3-8882-42ce54ebb75e
-- title:
--   SCPf: perm inr
-- statement:
--   The SCPf construction uses the perm inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LiftXHasSubst.lean#L130-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LiftXHasSubst.lean#L130-L144

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_WickFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.TB.SCPf.perm_inr (s : ι → Bool) :
    ((Finset.univ : Finset ι).toList.filter (fun l => !s l)).Perm
      (List.ofFn fun j => (sideE s).symm (Sum.inr j)) := by sorry
