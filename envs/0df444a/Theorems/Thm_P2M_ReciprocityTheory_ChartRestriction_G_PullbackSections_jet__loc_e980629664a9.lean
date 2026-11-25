-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_jet__loc_e980629664a9
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_jet__loc_e980629664a9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:20:24.770987+00:00
-- url     : https://prove2.me/theorems/c42c4993-0cb5-4805-8657-3a58c88b6ea2
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Pullback Sections jet  loc e980629664a9: P2 M Reciprocity Theory Chart Restriction G Pullback Sections jet  loc e980629664a9
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Pullback Sections jet  loc e980629664a9 construction uses the P2 M Reciprocity Theory Chart Restriction G Pullback Sections jet  loc e980629664a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetB.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetB.lean#L140-L143

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
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
variable {g : ℕ} {Y : Scheme.{0}}
variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)

theorem P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_jet__loc_e980629664a9 (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)) (hf : IsUnit (jetψ e hol m U hU f)) :
    e 0 cpt ∈ Y.basicOpen f := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«PullbackSections».«jetψ_loc» := P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_jet__loc_e980629664a9
