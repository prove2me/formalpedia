-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__specMap_50eff1d20a13
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__specMap_50eff1d20a13
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:05:03.317069+00:00
-- url     : https://prove2.me/theorems/e1085a24-cc4a-43d3-840a-74ceb3736ef4
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  spec Map 50eff1d20a13: P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  spec Map 50eff1d20a13
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  spec Map 50eff1d20a13 construction uses the P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  spec Map 50eff1d20a13 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolPairB.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolPairB.lean#L27-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairB
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
open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__specMap_50eff1d20a13 {A C : CommRingCat.{0}} (φ : A ⟶ C) (x : Sp ℂ ⟶ Spec C) (a : A) :
    valAt' (x ≫ Spec.map φ) ⊤ ((Scheme.ΓSpecIso A).inv a) = valAt' x ⊤ ((Scheme.ΓSpecIso C).inv (φ a)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«PullbackSections».«valAt'_specMap» := P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__specMap_50eff1d20a13
