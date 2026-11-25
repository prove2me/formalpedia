-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_range
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_range
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:18:01.643303+00:00
-- url     : https://prove2.me/theorems/9d8904aa-5506-406f-a533-8b8bbbe6c7a2
-- title:
--   Pullback Sections: vtf range
-- statement:
--   The Pullback Sections construction uses the vtf range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdHol.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdHol.lean#L44-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
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
open AlgebraicGeometry CategoryTheory Limits Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_range {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    Set.range x ⊆ Set.range U.ι := by sorry
