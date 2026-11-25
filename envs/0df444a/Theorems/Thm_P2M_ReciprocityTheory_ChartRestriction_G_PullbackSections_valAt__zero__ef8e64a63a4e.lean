-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__zero__ef8e64a63a4e
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__zero__ef8e64a63a4e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:22.279526+00:00
-- url     : https://prove2.me/theorems/cbea4fcd-3a82-4f17-9bbd-b9bdfe76a3c9
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  zero  ef8e64a63a4e: P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  zero  ef8e64a63a4e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  zero  ef8e64a63a4e construction uses the P2 M Reciprocity Theory Chart Restriction G Pullback Sections val At  zero  ef8e64a63a4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolPairB.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolPairB.lean#L35-L39

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__zero__ef8e64a63a4e {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (U : Y.Opens) : valAt' x U 0 = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«PullbackSections».«valAt'_zero'» := P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__zero__ef8e64a63a4e
