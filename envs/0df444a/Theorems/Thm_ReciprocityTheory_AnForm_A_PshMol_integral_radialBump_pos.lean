-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshMol_integral_radialBump_pos
-- name    : ReciprocityTheory.AnForm.A.PshMol.integral_radialBump_pos
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:05:17.803872+00:00
-- url     : https://prove2.me/theorems/541c9b79-8d57-4f99-a011-1b6799f5f3bb
-- title:
--   Psh Mol: integral radial Bump pos
-- statement:
--   The Psh Mol construction uses the integral radial Bump pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean#L206-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean#L206-L211

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

theorem ReciprocityTheory.AnForm.A.PshMol.integral_radialBump_pos (D : ℕ) : 0 < ∫ w, g0 D w := by sorry
