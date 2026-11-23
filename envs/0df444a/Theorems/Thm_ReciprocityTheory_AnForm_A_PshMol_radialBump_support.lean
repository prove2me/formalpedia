-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshMol_radialBump_support
-- name    : ReciprocityTheory.AnForm.A.PshMol.radialBump_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:16.416061+00:00
-- url     : https://prove2.me/theorems/49457b2b-6b6a-4afa-8d22-271671fa0e72
-- title:
--   Psh Mol: radial Bump support
-- statement:
--   The Psh Mol construction uses the radial Bump support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean#L185-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean#L185-L196

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

theorem ReciprocityTheory.AnForm.A.PshMol.radialBump_support (D : ℕ) : Function.support (g0 D) ⊆ ball 0 1 := by sorry
