-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_sameOrbit_of_segre
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.sameOrbit_of_segre
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:59.619182+00:00
-- url     : https://prove2.me/theorems/08e4de0b-7f51-426f-8615-65144acd4c54
-- title:
--   Geo: same Orbit of segre
-- statement:
--   The Geo construction uses the same Orbit of segre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeB.lean#L62-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeB.lean#L62-L84

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.sameOrbit_of_segre {z z' : (Σ k, ι k) → ℂ} (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (μ : ℂ)
    (hμ : μ ≠ 0) (h : segre z = μ • segre z') : SameOrbit z z' := by sorry
