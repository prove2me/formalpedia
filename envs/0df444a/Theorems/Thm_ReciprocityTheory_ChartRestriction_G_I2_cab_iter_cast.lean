-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_iter_cast
-- name    : ReciprocityTheory.ChartRestriction.G.I2.cab_iter_cast
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:50.055326+00:00
-- url     : https://prove2.me/theorems/f3d685bf-a918-4cf0-ab78-d6440a26edc4
-- title:
--   I2: cab iter cast
-- statement:
--   The I2 construction uses the cab iter cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelA.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelA.lean#L71-L74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.I2.cab_iter_cast {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (F : W → ℂ) (z : W)
    {n n' : ℕ} (h : n = n') (v : Fin n → W) :
    iteratedFDeriv ℂ n F z v = iteratedFDeriv ℂ n' F z (v ∘ Fin.cast h.symm) := by sorry
