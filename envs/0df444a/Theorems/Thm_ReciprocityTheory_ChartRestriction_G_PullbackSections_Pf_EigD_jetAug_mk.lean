-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_jetAug_mk
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.jetAug_mk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:56:15.816155+00:00
-- url     : https://prove2.me/theorems/5714f489-1309-5934-8ef7-b4488fa12852
-- title:
--   Eig D: jet Aug mk
-- statement:
--   The Eig D construction uses the jet Aug mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SubstTanSnd.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SubstTanSnd.lean#L25-L28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SingleMemDegLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SubstTanSnd
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
variable {V : Type} [CommRing V] {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.jetAug_mk {ι : Type} (q : MvPolynomial ι V) :
    jetAug (R := V) (m := 1) (Ideal.Quotient.mk _ q) = constantCoeff q := by sorry
