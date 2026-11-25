-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshMol_radialBump_smul
-- name    : ReciprocityTheory.AnForm.A.PshMol.radialBump_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:05:23.734942+00:00
-- url     : https://prove2.me/theorems/bc389a57-e559-52fb-914e-2c16cd1d7404
-- title:
--   Psh Mol: radial Bump smul
-- statement:
--   The Psh Mol construction uses the radial Bump smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean#L198-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean#L198-L199

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

theorem ReciprocityTheory.AnForm.A.PshMol.radialBump_smul (D : ℕ) (c : ℂ) (w : Fin D → ℂ) (hc : ‖c‖ = 1) : g0 D (c • w) = g0 D w := by sorry
