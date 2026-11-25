-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_vecMul_tmat_support
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.vecMul_tmat_support
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:18.470593+00:00
-- url     : https://prove2.me/theorems/95960ac6-aedb-494e-a110-08bb6426e628
-- title:
--   PTb: vec Mul tmat support
-- statement:
--   The PTb construction uses the vec Mul tmat support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/EqZeroOfVecMulTmat.lean#L90-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/EqZeroOfVecMulTmat.lean#L90-L117

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.vecMul_tmat_support {h : ℕ} (ty : Fin d → ZMod h) {γ : Fin d → Fin d → PowerSeries C}
    (hdet : v (tmat γ).det = 0) (ht : ∀ b c, ty c ≠ ty b → tangent (γ b) c = 0)
    (x : Fin d → C) (τ : ZMod h) (hw : ∀ c, ty c ≠ τ → Matrix.vecMul x (tmat γ) c = 0) :
    ∀ b, ty b ≠ τ → x b = 0 := by sorry
