-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_prod_update_eq
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.prod_update_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:22.848774+00:00
-- url     : https://prove2.me/theorems/9f189681-022d-4c27-b891-4a99d4ef4b3b
-- title:
--   Geo: prod update eq
-- statement:
--   The Geo construction uses the prod update eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetA.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetA.lean#L44-L50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
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
open MvPolynomial Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.prod_update_eq [DecidableEq K] (z : (Σ k, ι k) → ℂ) (i0 : (k : K) → ι k) (k : K) (i : ι k) :
    ∏ k', z ⟨k', Function.update i0 k i k'⟩ = z ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ := by sorry
