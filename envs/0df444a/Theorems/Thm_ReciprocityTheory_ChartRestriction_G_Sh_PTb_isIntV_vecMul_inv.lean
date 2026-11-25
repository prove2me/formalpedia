-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isIntV_vecMul_inv
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.isIntV_vecMul_inv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:31.57201+00:00
-- url     : https://prove2.me/theorems/68bf9ccc-748e-5d88-addc-b415d4f7ebdd
-- title:
--   PTb: is Int V vec Mul inv
-- statement:
--   The PTb construction uses the is Int V vec Mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/EqZeroOfVecMulTmat.lean#L73-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/EqZeroOfVecMulTmat.lean#L73-L88

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.isIntV_vecMul_inv {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a))
    (hdet : v (tmat γ).det = 0) {w : Fin d → C} (hw : ∀ c, IsIntV v (w c)) (b : Fin d) :
    IsIntV v (Matrix.vecMul w (tmat γ)⁻¹ b) := by sorry
