-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomogIdeal_of_isHomogeneous
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_of_isHomogeneous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:42.214038+00:00
-- url     : https://prove2.me/theorems/c4e52c23-4970-4614-b74f-07aefbfb4c56
-- title:
--   Geo: is Multi Homog Ideal of is Homogeneous
-- statement:
--   The Geo construction uses the is Multi Homog Ideal of is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean#L104-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean#L104-L133

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
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_of_isHomogeneous [DecidableEq K] {W : Ideal (MRing ι)}
    (hW : ∀ k, W.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blockWeight (ι := ι) k))) :
    IsMultiHomogIdeal W := by sorry
