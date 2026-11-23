-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_sumF
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.isCurve_sumF
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:57.168946+00:00
-- url     : https://prove2.me/theorems/540b1278-1c54-4242-9872-de1c7983ae03
-- title:
--   PTb: is Curve sum F
-- statement:
--   The PTb construction uses the is Curve sum F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean#L172-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean#L172-L176

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.isCurve_sumF (G : LogFGL v d) {m : ℕ} (g : Fin m → Fin d → PowerSeries C)
    (h : ∀ u, IsCurve v (g u)) : IsCurve v (G.sumF g) := by sorry
