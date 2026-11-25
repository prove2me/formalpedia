-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sum_fin_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.sum_fin_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:34:57.696214+00:00
-- url     : https://prove2.me/theorems/bb5aea53-8f07-4ae1-8100-0036fc0671c5
-- title:
--   I2: sum fin le
-- statement:
--   The I2 construction uses the sum fin le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/L2NormSqNonnegGaussianTorus.lean#L33-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/L2NormSqNonnegGaussianTorus.lean#L33-L47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormSqNonnegGaussianTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.I2.sum_fin_le {M : Type*} [AddCommMonoid M] {ρ N : ℕ} (h : ρ ≤ N) (f : Fin ρ → M) :
    ∑ k : Fin N, (if h' : k.val < ρ then f ⟨k, h'⟩ else 0) = ∑ s, f s := by sorry
