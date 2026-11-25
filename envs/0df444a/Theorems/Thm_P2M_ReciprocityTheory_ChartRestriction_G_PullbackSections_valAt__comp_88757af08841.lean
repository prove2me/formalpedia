-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__comp_88757af08841
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__comp_88757af08841
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:36.540731+00:00
-- url     : https://prove2.me/theorems/7ca54cb9-f371-4dec-972c-8f61082a8f13
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  comp 88757af08841: P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  comp 88757af08841
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  comp 88757af08841 construction uses the P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  comp 88757af08841 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetC.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetC.lean#L14-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
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

theorem P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__comp_88757af08841 (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Y') (U : Y'.Opens) (f : Γ(Y', U)) :
    valAt' x (φ ⁻¹ᵁ U) (φ.app U f) = valAt' (x ≫ φ) U f := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«PullbackSections».«valAt'_comp» := P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__comp_88757af08841
