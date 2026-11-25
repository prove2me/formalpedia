-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_circ_smul
-- name    : ReciprocityTheory.AnForm.A.PshLap.circ_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:05:02.359541+00:00
-- url     : https://prove2.me/theorems/7ca1e5ad-0da0-4045-bec2-2f66d337b75d
-- title:
--   Psh Lap: circ smul
-- statement:
--   The Psh Lap construction uses the circ smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L62-L66

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {D : ℕ}
variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}

theorem ReciprocityTheory.AnForm.A.PshLap.circ_smul (r θ : ℝ) (w : Fin D → ℂ) :
    circleMap 0 r θ • w = circleMap 0 1 θ • ((r:ℂ) • w) := by sorry
