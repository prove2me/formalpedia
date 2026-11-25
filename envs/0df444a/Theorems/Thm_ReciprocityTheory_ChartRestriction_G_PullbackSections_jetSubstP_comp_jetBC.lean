-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetSubstP_comp_jetBC
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jetSubstP_comp_jetBC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:53.939991+00:00
-- url     : https://prove2.me/theorems/8be40ab2-3510-4aea-a0e1-801daa6bcfe1
-- title:
--   Pullback Sections: jet Subst P comp jet BC
-- statement:
--   The Pullback Sections construction uses the jet Subst P comp jet BC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/JetSubstPCompJetBC.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/JetSubstPCompJetBC.lean#L57-L66

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jetSubstP_comp_jetBC {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) :
    (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) : Jet S' κ m →ₐ[S'] Jet S' κ' m).toRingHom.comp (jetBC ψ κ m) =
      (jetBC ψ κ' m).comp (jetSubstP m φ : Jet S κ m →ₐ[S] Jet S κ' m).toRingHom := by sorry
