-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_vecMul_inv_tmat
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.vecMul_inv_tmat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:07.49223+00:00
-- url     : https://prove2.me/theorems/a1a7d107-4a12-4934-9916-2ba46426a97a
-- title:
--   PTb: vec Mul inv tmat
-- statement:
--   The PTb construction uses the vec Mul inv tmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/EqZeroOfVecMulTmat.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/EqZeroOfVecMulTmat.lean#L62-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.vecMul_inv_tmat {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0)
    (w : Fin d → C) : Matrix.vecMul (Matrix.vecMul w (tmat γ)⁻¹) (tmat γ) = w := by sorry
