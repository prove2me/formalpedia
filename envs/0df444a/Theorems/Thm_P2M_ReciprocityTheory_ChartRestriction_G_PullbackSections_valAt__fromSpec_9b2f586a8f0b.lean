-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__fromSpec_9b2f586a8f0b
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__fromSpec_9b2f586a8f0b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:25:46.271743+00:00
-- url     : https://prove2.me/theorems/884685ae-707b-4496-8ffe-dea02dc44257
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  from Spec 9b2f586a8f0b: P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  from Spec 9b2f586a8f0b
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  from Spec 9b2f586a8f0b construction uses the P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  from Spec 9b2f586a8f0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolPair.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolPair.lean#L16-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPair
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
open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__fromSpec_9b2f586a8f0b {Y : Scheme.{0}} {Vo : Y.Opens} (hV : IsAffineOpen Vo) (l : Sp ℂ ⟶ Spec Γ(Y, Vo))
    (a : Γ(Y, Vo)) : valAt' (l ≫ hV.fromSpec) Vo a = valAt' l ⊤ ((Scheme.ΓSpecIso Γ(Y, Vo)).inv a) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«PullbackSections».«valAt'_fromSpec» := P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__fromSpec_9b2f586a8f0b
