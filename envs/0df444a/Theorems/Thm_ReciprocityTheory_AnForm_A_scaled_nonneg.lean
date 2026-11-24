-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_nonneg
-- name    : ReciprocityTheory.AnForm.A.scaled_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:55.201532+00:00
-- url     : https://prove2.me/theorems/b2b5c856-2988-4749-bdd8-0da0731c5723
-- title:
--   A: scaled nonneg
-- statement:
--   The A construction uses the scaled nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollA.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollA.lean#L19-L20

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

theorem ReciprocityTheory.AnForm.A.scaled_nonneg {ε : ℝ} (hε : 0 < ε) (w : Fin D → ℂ) : 0 ≤ ρ.scaled ε w := by sorry
