-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_isCurve_iff_good
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.isCurve_iff_good
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:22.696801+00:00
-- url     : https://prove2.me/theorems/c6f17677-32ed-4d8a-8ded-03ff77429a85
-- title:
--   Sh: is Curve iff good
-- statement:
--   The Sh construction uses the is Curve iff good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/NsmulCoprimeBijectiveCurves.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/NsmulCoprimeBijectiveCurves.lean#L76-L81

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.isCurve_iff_good {ga : Fin d → PowerSeries C} : IsCurve v ga ↔ PTGood v ga := by sorry
