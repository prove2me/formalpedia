-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_block_deg_of_scale
-- name    : ReciprocityTheory.ChartRestriction.G.T0.block_deg_of_scale
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:37:44.67984+00:00
-- url     : https://prove2.me/theorems/f6816ead-68fb-5510-9b5f-6bde12448549
-- title:
--   T0: block deg of scale
-- statement:
--   The T0 construction uses the block deg of scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/BlockDegOfScale.lean#L42-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/BlockDegOfScale.lean#L42-L55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K : Type} [Field K] {D N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.block_deg_of_scale [CharZero K] (b : Fin (D + 1)) (a : ℕ) (F : MvPolynomial (TVar D N) K)
    (hF : ∀ u : Kˣ, scaleEquiv (fun v : TVar D N => v.1 = b) u F = C ((u : K) ^ a) * F) :
    ∀ s ∈ F.support, ∑ j, s (b, j) = a := by sorry
