-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_phiPow_indep
-- name    : ReciprocityTheory.ChartRestriction.G.H1.phiPow_indep
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:26:30.800403+00:00
-- url     : https://prove2.me/theorems/7c1ee326-4a9d-4e29-90f3-1c7f77dea4f4
-- title:
--   H1: phi Pow indep
-- statement:
--   The H1 construction uses the phi Pow indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/PhiPowAlg.lean#L62-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/PhiPowAlg.lean#L62-L101

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem ReciprocityTheory.ChartRestriction.G.H1.phiPow_indep (h : IsCub θ) (k : ℕ) (a b : A) :
    (∏ i ∈ Finset.range k, hv θ k (a * (b ^ k) ^ i) b (b ^ (k - 1 - i))) * cubN θ k 1 b a *
        (∏ i ∈ Finset.range k, θ a ((b ^ k) ^ i) b)⁻¹ =
      ∏ i ∈ Finset.range k, hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) := by sorry
