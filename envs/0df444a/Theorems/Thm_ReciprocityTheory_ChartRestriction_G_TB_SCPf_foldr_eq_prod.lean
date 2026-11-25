-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_foldr_eq_prod
-- name    : ReciprocityTheory.ChartRestriction.G.TB.SCPf.foldr_eq_prod
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:50.464247+00:00
-- url     : https://prove2.me/theorems/83fc6d57-448a-54c5-8bf4-afac76c0330b
-- title:
--   SCPf: foldr eq prod
-- statement:
--   The SCPf construction uses the foldr eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LiftXHasSubst.lean#L105-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LiftXHasSubst.lean#L105-L113

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

theorem ReciprocityTheory.ChartRestriction.G.TB.SCPf.foldr_eq_prod (f : ι → AA k d → AA k d) (F : ι → Module.End k (AA k d)) (hF : ∀ l, ⇑(F l) = f l)
    (n : ι →₀ ℕ) (L : List ι) (G : AA k d) :
    L.foldr (fun l g => (f l)^[n l] g) G = (L.map fun l => F l ^ n l).prod G := by sorry
