-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetAug_comp_jetBC
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jetAug_comp_jetBC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:48.337975+00:00
-- url     : https://prove2.me/theorems/88c30e84-6bc0-4a54-9375-d49892242a24
-- title:
--   Pullback Sections: jet Aug comp jet BC
-- statement:
--   The Pullback Sections construction uses the jet Aug comp jet BC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/JetSubstPCompJetBC.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/JetSubstPCompJetBC.lean#L16-L19

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jetAug_comp_jetBC (κ : Type) (m : ℕ) :
    (jetAug : Jet S' κ m →ₐ[S'] S').toRingHom.comp (jetBC ψ κ m) = ψ.comp (jetAug : Jet S κ m →ₐ[S] S).toRingHom := by sorry
