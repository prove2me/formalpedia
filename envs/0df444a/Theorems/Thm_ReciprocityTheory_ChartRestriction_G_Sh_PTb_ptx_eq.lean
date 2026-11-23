-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_ptx_eq
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.ptx_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:34.632056+00:00
-- url     : https://prove2.me/theorems/8fe16516-8a42-4060-b6f0-9c738e47b7f5
-- title:
--   PTb: ptx eq
-- statement:
--   The PTb construction uses the ptx eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/LgCurvePcurve.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/LgCurvePcurve.lean#L25-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_LgCurvePcurve
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
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.ptx_eq (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C)
    (ga : Fin d → PowerSeries C) (n : ℕ) :
    ptx G p γ ga n = Matrix.vecMul (ptw G p γ ga n) (tmat γ)⁻¹ := by sorry
