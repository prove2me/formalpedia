-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_weight_blockWeight
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.weight_blockWeight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:46.713706+00:00
-- url     : https://prove2.me/theorems/ba971b9d-56e3-491f-82c8-4d691a12817b
-- title:
--   Geo: weight block Weight
-- statement:
--   The Geo construction uses the weight block Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean#L52-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppA
import Definitions.Def_Lemmata_GeneralBFactTerForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
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

theorem ReciprocityTheory.ChartRestriction.G.Geo.weight_blockWeight [DecidableEq K] (k : K) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight (ι := ι) k) m = ∑ i, m ⟨k, i⟩ := by sorry
