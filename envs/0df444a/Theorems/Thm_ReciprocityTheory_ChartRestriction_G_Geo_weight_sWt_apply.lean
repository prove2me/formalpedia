-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_weight_sWt_apply
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.weight_sWt_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:25:34.333877+00:00
-- url     : https://prove2.me/theorems/ea49b405-0e2c-4a2e-8ede-58a7b24468fb
-- title:
--   Geo: weight s Wt apply
-- statement:
--   The Geo construction uses the weight s Wt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodF.lean#L103-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodF.lean#L103-L122

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (k0 : K)

theorem ReciprocityTheory.ChartRestriction.G.Geo.weight_sWt_apply {r : ℕ} (n : (Fin r ⊕ {k // k ≠ k0}) →₀ ℕ) (k : K) :
    Finsupp.weight (sWt k0 r) n k =
      (∑ j, n (Sum.inl j)) + (if h : k = k0 then 0 else n (Sum.inr ⟨k, h⟩)) := by sorry
