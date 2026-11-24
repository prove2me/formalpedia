-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eq_bsmul_of_segre_eq
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.eq_bsmul_of_segre_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:41.592206+00:00
-- url     : https://prove2.me/theorems/beef613b-6b58-41bb-a17c-1857a5a7a05b
-- title:
--   Geo: eq bsmul of segre eq
-- statement:
--   The Geo construction uses the eq bsmul of segre eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetA.lean#L52-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetA.lean#L52-L77

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.eq_bsmul_of_segre_eq {z z' : (Σ k, ι k) → ℂ} (i0 : (k : K) → ι k)
    (h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0) (hs : segre z = segre z') :
    (∀ k, z' ⟨k, i0 k⟩ ≠ 0) ∧ z' = bsmul (fun k => z' ⟨k, i0 k⟩ / z ⟨k, i0 k⟩) z := by sorry
