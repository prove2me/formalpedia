-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_SmallOperatorExistence_opN_le
-- name    : ReciprocityTheory.ChartRestriction.G.FD.SmallOperatorExistence.opN_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:50:06.438567+00:00
-- url     : https://prove2.me/theorems/fce2c882-f4e4-4057-bcec-2bcfedcbe302
-- title:
--   Small Operator Existence: op N le
-- statement:
--   The Small Operator Existence construction uses the op N le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SmallOperatorExistence.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SmallOperatorExistence.lean#L10-L21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOrthogonality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SmallOperatorExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.SmallOperatorExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.FD.SmallOperatorExistence.opN_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ v, OrthonormalChartBounds.nsq (A *ᵥ v) ≤ δ ^ 2 * OrthonormalChartBounds.nsq v) : Data.opN A ≤ δ := by sorry
