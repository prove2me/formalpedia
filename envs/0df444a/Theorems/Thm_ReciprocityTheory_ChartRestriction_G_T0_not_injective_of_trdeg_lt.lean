-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_not_injective_of_trdeg_lt
-- name    : ReciprocityTheory.ChartRestriction.G.T0.not_injective_of_trdeg_lt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:15:33.078867+00:00
-- url     : https://prove2.me/theorems/e1d808fa-0f66-44c7-95ba-d0e8bb27092c
-- title:
--   T0: not injective of trdeg lt
-- statement:
--   The T0 construction uses the not injective of trdeg lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/BlockSphereProbIsProbabilityMeasure.lean#L69-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/BlockSphereProbIsProbabilityMeasure.lean#L69-L94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockSphereProbIsProbabilityMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField

theorem ReciprocityTheory.ChartRestriction.G.T0.not_injective_of_trdeg_lt {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {σ τ : Type}
    [Fintype σ] [Fintype τ] (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ Ω) (n : ℕ)
    (hn : Algebra.trdeg K Ω = n) (hlt : n + Fintype.card τ < Fintype.card σ) :
    ¬ Function.Injective φ := by sorry
