-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_qIdeal_isHomogeneous
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.qIdeal_isHomogeneous
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:25:25.278023+00:00
-- url     : https://prove2.me/theorems/b126bb70-017f-5edc-91de-1c408bac632f
-- title:
--   Geo: q Ideal is Homogeneous
-- statement:
--   The Geo construction uses the q Ideal is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodF.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodF.lean#L43-L50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
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
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.qIdeal_isHomogeneous (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) :
    (qIdeal P).IsHomogeneous (weightedHomogeneousSubmodule ℚ (blkWt (ι := ι))) := by sorry
