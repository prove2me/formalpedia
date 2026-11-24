-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isWeightedHomogeneous_cycBlockWt
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.isWeightedHomogeneous_cycBlockWt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:33.502435+00:00
-- url     : https://prove2.me/theorems/35f015b0-088e-4ff1-ab93-5d0e2a83b4c9
-- title:
--   I1: is Weighted Homogeneous cyc Block Wt
-- statement:
--   The I1 construction uses the is Weighted Homogeneous cyc Block Wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean#L27-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_Lemmata_GeneralBFactBis_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.isWeightedHomogeneous_cycBlockWt [DecidableEq K] {s : MRingOver R ι} {a : K → ℕ}
    (h : IsMultiHomog s a) (k : K) : IsWeightedHomogeneous (cycBlockWt (ι := ι) k) s (a k) := by sorry
