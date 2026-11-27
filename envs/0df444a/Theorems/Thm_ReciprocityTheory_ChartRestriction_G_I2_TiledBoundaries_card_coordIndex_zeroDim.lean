-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_card_coordIndex_zeroDim
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.card_coordIndex_zeroDim
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:13:58.039658+00:00
-- url     : https://prove2.me/theorems/757f1dc4-11cd-4151-aa2d-c82436a998ae
-- title:
--   Tiled Boundaries: card coord Index zero Dim
-- statement:
--   The Tiled Boundaries construction uses the card coord Index zero Dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/NstatementHypsConsistent.lean#L25-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/NstatementHypsConsistent.lean#L25-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 NumberField Complex
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.card_coordIndex_zeroDim : Fintype.card (Idx dim0) = 0 := by sorry
