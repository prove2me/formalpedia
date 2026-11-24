-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.scaleBlock_mem_zeroLocus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:24.659983+00:00
-- url     : https://prove2.me/theorems/e3e1ff85-8335-4125-af93-21f579227051
-- title:
--   Geo: scale Block mem zero Locus
-- statement:
--   The Geo construction uses the scale Block mem zero Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGood.lean#L33-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGood.lean#L33-L49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.scaleBlock_mem_zeroLocus (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) (k0 : K) {c : ℂ} (hc : c ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : scaleBlock k0 c z ∈ mcPts P := by sorry
