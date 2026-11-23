-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_rescale
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_rescale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:11.376543+00:00
-- url     : https://prove2.me/theorems/44b9f906-b2cf-4dcd-9dfe-ee6f787b4440
-- title:
--   PTb: lg Curve rescale
-- statement:
--   The PTb construction uses the lg Curve rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean#L199-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean#L199-L206

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_rescale (G : LogFGL v d) (x : C) {ga : Fin d → PowerSeries C}
    (h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0) (a : Fin d) :
    G.lgCurve (rescaleCurve x ga) a = PowerSeries.rescale x (G.lgCurve ga a) := by sorry
