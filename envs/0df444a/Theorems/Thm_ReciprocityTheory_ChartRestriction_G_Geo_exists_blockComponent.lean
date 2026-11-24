-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_blockComponent
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.exists_blockComponent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:00.983515+00:00
-- url     : https://prove2.me/theorems/dffa5355-efbe-4066-b6a1-366b1f130057
-- title:
--   Geo: exists block Component
-- statement:
--   The Geo construction uses the exists block Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean#L90-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean#L90-L102

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.exists_blockComponent [DecidableEq K] {W : Ideal (MRing ι)}
    (hW : ∀ k, W.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blockWeight (ι := ι) k)))
    (a : K → ℕ) (T : Finset K) {f : MRing ι} (hf : f ∈ W) :
    ∃ g ∈ W, ∀ m, coeff m g = if (∀ k ∈ T, ∑ i, m ⟨k, i⟩ = a k) then coeff m f else 0 := by sorry
