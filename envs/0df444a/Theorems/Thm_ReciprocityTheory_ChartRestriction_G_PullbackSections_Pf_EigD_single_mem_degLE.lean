-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_single_mem_degLE
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.single_mem_degLE
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:34:21.120943+00:00
-- url     : https://prove2.me/theorems/b7c9d17c-48bb-5bb8-b097-35e4a0791aa3
-- title:
--   Eig D: single mem deg LE
-- statement:
--   The Eig D construction uses the single mem deg LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SingleMemDegLE.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SingleMemDegLE.lean#L40-L47

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SingleMemDegLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
open MvPolynomial CategoryTheory Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G
attribute [local instance] Over.cartesianMonoidalCategory
variable {V : Type} [CommRing V]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.single_mem_degLE {ι : Type} [Fintype ι] [DecidableEq ι] (ℓ : ι) : Finsupp.single ℓ 1 ∈ degLE (ι := ι) 1 := by sorry
