-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptOn_good
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptOn_good
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:56.670798+00:00
-- url     : https://prove2.me/theorems/d2a4c425-137c-49e9-9d03-c4c782c22c0d
-- title:
--   Sh: pt On good
-- statement:
--   The Sh construction uses the pt On good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtBasisMapGood.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtBasisMapGood.lean#L24-L33

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptOn_good (a : Fin d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) :
    PTGood v (ptOn a ga) := by sorry
