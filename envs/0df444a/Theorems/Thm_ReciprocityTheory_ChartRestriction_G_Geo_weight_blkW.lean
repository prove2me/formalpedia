-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_weight_blkW
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.weight_blkW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:31.428992+00:00
-- url     : https://prove2.me/theorems/c4b3bbe3-4328-4560-9cb7-d54c0cc53476
-- title:
--   Geo: weight blk W
-- statement:
--   The Geo construction uses the weight blk W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFibB.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFibB.lean#L15-L18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibB
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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.weight_blkW (β : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blkW ι) β k = ∑ i, β ⟨k, i⟩ := by sorry
