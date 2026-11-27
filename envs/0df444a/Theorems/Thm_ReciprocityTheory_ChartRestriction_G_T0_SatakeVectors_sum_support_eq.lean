-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_sum_support_eq
-- name    : ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.sum_support_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:42:50.455799+00:00
-- url     : https://prove2.me/theorems/9e77026c-8360-5e04-ad7a-4d54595e8beb
-- title:
--   Satake Vectors: sum support eq
-- statement:
--   The Satake Vectors construction uses the sum support eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L268-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L268-L278

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.sum_support_eq {κ : Type} {T : Finset (κ →₀ ℕ)} {r : ℕ} (e : T ≃ Fin r)
    (P Q : MvPolynomial κ ℂ) (hP : P.support ⊆ T) :
    ∑ s ∈ P.support, P.coeff s * star (Q.coeff s) =
      ∑ i : Fin r, P.coeff (e.symm i : κ →₀ ℕ) * star (Q.coeff (e.symm i : κ →₀ ℕ)) := by sorry
