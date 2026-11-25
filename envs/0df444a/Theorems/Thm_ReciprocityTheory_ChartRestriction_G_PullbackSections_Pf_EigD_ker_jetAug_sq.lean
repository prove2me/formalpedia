-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_ker_jetAug_sq
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.ker_jetAug_sq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:40:50.775823+00:00
-- url     : https://prove2.me/theorems/aa9f42a2-f940-5204-ad6a-f5ba8c0036f2
-- title:
--   Eig D: ker jet Aug sq
-- statement:
--   The Eig D construction uses the ker jet Aug sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SingleMemDegLE.lean#L49-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SingleMemDegLE.lean#L49-L50

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.ker_jetAug_sq {κ : Type} : (RingHom.ker (jetAug (R := V) (ι := κ) (m := 1))) ^ (1 + 1) = ⊥ := by sorry
