-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetMap_comp_jetBC
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jetMap_comp_jetBC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:42:16.616847+00:00
-- url     : https://prove2.me/theorems/85757a46-5adc-492d-badc-798b6e352b93
-- title:
--   Pullback Sections: jet Map comp jet BC
-- statement:
--   The Pullback Sections construction uses the jet Map comp jet BC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/JetSubstPCompJetBC.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/JetSubstPCompJetBC.lean#L41-L50

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jetMap_comp_jetBC {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (hφ : ∀ i, φ i ∈ orig S κ')
    (hφ' : ∀ i, MvPolynomial.map ψ (φ i) ∈ orig S' κ') :
    (jetMap (m := m) (fun i => MvPolynomial.map ψ (φ i)) hφ').toRingHom.comp (jetBC ψ κ m) =
      (jetBC ψ κ' m).comp (jetMap (m := m) φ hφ).toRingHom := by sorry
