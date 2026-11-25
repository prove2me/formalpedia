-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptOn_lg
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptOn_lg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:36:11.78985+00:00
-- url     : https://prove2.me/theorems/b91403b2-201f-52fc-8702-cee62540d363
-- title:
--   Sh: pt On lg
-- statement:
--   The Sh construction uses the pt On lg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtBasisMapGood.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtBasisMapGood.lean#L43-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtBasisMapGood
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

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptOn_lg (G : LogFGL v d) (a : Fin d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga)
    (b : Fin d) :
    subst (ptOn a ga) (G.lg b) = PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve ga b) := by sorry
