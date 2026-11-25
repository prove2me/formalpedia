-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_const
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_const
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:23:14.23904+00:00
-- url     : https://prove2.me/theorems/12dd1839-856e-4772-af34-3767448681fe
-- title:
--   Pullback Sections: jet Pt const
-- statement:
--   The Pullback Sections construction uses the jet Pt const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetE.lean#L33-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetE.lean#L33-L56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
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
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {g : ℕ} {Y Y' : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_const (u : Sp ℂ ⟶ Y) (m : ℕ) :
    spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) ≫ u = jetPt (fun _ => u) (isHolFam_const u) m := by sorry
