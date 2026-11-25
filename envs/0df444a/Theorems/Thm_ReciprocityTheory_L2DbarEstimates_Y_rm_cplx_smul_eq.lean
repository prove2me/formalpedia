-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rm_cplx_smul_eq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.rm_cplx_smul_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:01:35.235883+00:00
-- url     : https://prove2.me/theorems/3082989c-4154-4dd9-a151-99ce3fc5aead
-- title:
--   Y: rm cplx smul eq
-- statement:
--   The Y construction uses the rm cplx smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L212-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L212-L214

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.Y.rm_cplx_smul_eq (z : ℂ) (x : V n) : z • x = z.re • x + z.im • (Complex.I • x) := by sorry
