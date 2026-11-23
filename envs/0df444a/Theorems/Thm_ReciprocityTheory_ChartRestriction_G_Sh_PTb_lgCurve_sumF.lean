-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_sumF
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_sumF
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:15.525901+00:00
-- url     : https://prove2.me/theorems/b9a35a73-bad5-4553-a0af-ee77aefb4759
-- title:
--   PTb: lg Curve sum F
-- statement:
--   The PTb construction uses the lg Curve sum F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean#L178-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean#L178-L185

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_sumF (G : LogFGL v d) {m : ℕ} (g : Fin m → Fin d → PowerSeries C)
    (h : ∀ u, IsCurve v (g u)) (a : Fin d) :
    G.lgCurve (G.sumF g) a = ∑ u, G.lgCurve (g u) a := by sorry
