-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isWeightedHomogeneous_of_isMultiHomog
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.isWeightedHomogeneous_of_isMultiHomog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:52.451946+00:00
-- url     : https://prove2.me/theorems/0b340a5f-2151-4ffd-9148-66ebc1e6a7cb
-- title:
--   Geo: is Weighted Homogeneous of is Multi Homog
-- statement:
--   The Geo construction uses the is Weighted Homogeneous of is Multi Homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean#L61-L65

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.isWeightedHomogeneous_of_isMultiHomog [DecidableEq K] {s : MRing ι} {a : K → ℕ}
    (h : IsMultiHomog s a) (k : K) : IsWeightedHomogeneous (blockWeight (ι := ι) k) s (a k) := by sorry
