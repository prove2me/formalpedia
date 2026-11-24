-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.mcPts_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:44.612133+00:00
-- url     : https://prove2.me/theorems/9881f7b7-34cf-4e45-bbf0-2877b660fa28
-- title:
--   Geo: mc Pts smul
-- statement:
--   The Geo construction uses the mc Pts smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeB.lean#L26-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeB.lean#L26-L41

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.mcPts_smul {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts J) :
    (fun p => c p.1 * z p) ∈ mcPts J := by sorry
