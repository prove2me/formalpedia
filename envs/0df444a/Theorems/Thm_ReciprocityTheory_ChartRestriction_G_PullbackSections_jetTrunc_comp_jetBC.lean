-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetTrunc_comp_jetBC
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jetTrunc_comp_jetBC
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:33:53.287976+00:00
-- url     : https://prove2.me/theorems/e4a19911-8823-5142-9eb1-85907804a286
-- title:
--   Pullback Sections: jet Trunc comp jet BC
-- statement:
--   The Pullback Sections construction uses the jet Trunc comp jet BC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/JetSubstPCompJetBC.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/JetSubstPCompJetBC.lean#L21-L25

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jetTrunc_comp_jetBC (κ : Type) (m : ℕ) :
    (jetTrunc : Jet S' κ (m + 1) →ₐ[S'] Jet S' κ m).toRingHom.comp (jetBC ψ κ (m + 1)) =
      (jetBC ψ κ m).comp (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m).toRingHom := by sorry
