-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_nsmulF_eq_subst
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.nsmulF_eq_subst
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:24.707846+00:00
-- url     : https://prove2.me/theorems/9c0e0727-bea6-5b33-b634-657788c04da7
-- title:
--   Sh: nsmul F eq subst
-- statement:
--   The Sh construction uses the nsmul F eq subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/NsmulCoprimeBijectiveCurves.lean#L60-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/NsmulCoprimeBijectiveCurves.lean#L60-L74

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_NsmulCoprimeBijectiveCurves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Sh.nsmulF_eq_subst (G : LogFGL v d) {ga : Fin d → PowerSeries C}
    (hga : HasSubst ga) : ∀ n, G.nsmulF n ga = fun a => subst ga (ptNs G n a)
  := by sorry
