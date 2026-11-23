-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoE_bchar_ne
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:44.025477+00:00
-- url     : https://prove2.me/theorems/9c4d3f63-d56a-44d7-b8ad-a3b75507af8a
-- title:
--   Onto E: bchar ne
-- statement:
--   The Onto E construction uses the bchar ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/OntoStatementPfE.lean#L21-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/OntoStatementPfE.lean#L21-L32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
open scoped ComplexConjugate ContDiff ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne (la : Wt X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : bchar la b ≠ 0 := by sorry
