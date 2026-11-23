-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshMol_radialBump_contDiff
-- name    : ReciprocityTheory.AnForm.A.PshMol.radialBump_contDiff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:09.3099+00:00
-- url     : https://prove2.me/theorems/3b93c486-3b10-4a47-a2fd-ffd556c580d2
-- title:
--   Psh Mol: radial Bump cont Diff
-- statement:
--   The Psh Mol construction uses the radial Bump cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean#L180-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean#L180-L181

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open MeasureTheory Metric Set Filter Topology Real
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshMol
noncomputable section

theorem ReciprocityTheory.AnForm.A.PshMol.radialBump_contDiff (D : ℕ) : ContDiff ℝ ∞ (g0 D) := by sorry
