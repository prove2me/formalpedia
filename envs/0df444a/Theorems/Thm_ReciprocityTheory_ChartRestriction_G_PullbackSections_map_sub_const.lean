-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_map_sub_const
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.map_sub_const
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:33:55.953277+00:00
-- url     : https://prove2.me/theorems/cfedf0b7-ed16-4b94-96f1-17dad0e5ca73
-- title:
--   Pullback Sections: map sub const
-- statement:
--   The Pullback Sections construction uses the map sub const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/JetSubstPCompJetBC.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/JetSubstPCompJetBC.lean#L52-L55

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.map_sub_const {κ : Type} (P : MvPolynomial κ S) :
    MvPolynomial.map ψ (P - C (MvPolynomial.constantCoeff P)) =
      MvPolynomial.map ψ P - C (MvPolynomial.constantCoeff (MvPolynomial.map ψ P)) := by sorry
