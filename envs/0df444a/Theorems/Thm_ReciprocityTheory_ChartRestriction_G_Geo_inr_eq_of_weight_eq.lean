-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_inr_eq_of_weight_eq
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.inr_eq_of_weight_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:17.734419+00:00
-- url     : https://prove2.me/theorems/1692a21b-b581-49ac-86c4-27c51ec91f5c
-- title:
--   Geo: inr eq of weight eq
-- statement:
--   The Geo construction uses the inr eq of weight eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodF.lean#L124-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodF.lean#L124-L131

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.inr_eq_of_weight_eq {r : ℕ} {n n0 : (Fin r ⊕ {k // k ≠ k0}) →₀ ℕ}
    (h : Finsupp.weight (sWt k0 r) n = Finsupp.weight (sWt k0 r) n0) (k' : {k // k ≠ k0}) :
    n (Sum.inr k') = n0 (Sum.inr k') := by sorry
