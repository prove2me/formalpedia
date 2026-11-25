-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoG_amgm
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG.amgm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:27:27.906858+00:00
-- url     : https://prove2.me/theorems/d7b9163a-fca3-4dc1-a670-f102ea65273a
-- title:
--   Onto G: amgm
-- statement:
--   The Onto G construction uses the amgm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/OntoStatementPfG.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/OntoStatementPfG.lean#L10-L15

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG
open MeasureTheory
open scoped ENNReal ComplexConjugate
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG.amgm {k x y : ℝ} (hk : 0 < k) : x * y ≤ (x ^ 2 / k + k * y ^ 2) / 2 := by sorry
