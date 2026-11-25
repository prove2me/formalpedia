-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_add
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:51.555421+00:00
-- url     : https://prove2.me/theorems/8eb079b8-a295-4b63-b19e-2da0bdd4b0f4
-- title:
--   PTb: lg Curve add
-- statement:
--   The PTb construction uses the lg Curve add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean#L118-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean#L118-L135

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_add (G : LogFGL v d) {ga gb : Fin d → PowerSeries C}
    (ha : ∀ b, PowerSeries.constantCoeff (ga b) = 0)
    (hb : ∀ b, PowerSeries.constantCoeff (gb b) = 0) (a : Fin d) :
    G.lgCurve (G.add ga gb) a = G.lgCurve ga a + G.lgCurve gb a := by sorry
