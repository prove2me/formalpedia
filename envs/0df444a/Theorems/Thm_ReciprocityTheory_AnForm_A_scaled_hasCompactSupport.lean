-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_hasCompactSupport
-- name    : ReciprocityTheory.AnForm.A.scaled_hasCompactSupport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:37.452496+00:00
-- url     : https://prove2.me/theorems/a1150681-fced-4319-9e7d-7cb56eb1d4c3
-- title:
--   A: scaled has Compact Support
-- statement:
--   The A construction uses the scaled has Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollA.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollA.lean#L40-L42

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D)

theorem ReciprocityTheory.AnForm.A.scaled_hasCompactSupport {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (ρ.scaled ε) := by sorry
