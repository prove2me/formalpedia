-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_Hc_apply
-- name    : ReciprocityTheory.AnForm.A.PshLap.Hc_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:05:05.715206+00:00
-- url     : https://prove2.me/theorems/528f8fed-bb63-4ada-96f2-80b37a54998d
-- title:
--   Psh Lap: Hc apply
-- statement:
--   The Psh Lap construction uses the Hc apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L29-L31

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

theorem ReciprocityTheory.AnForm.A.PshLap.Hc_apply (φ : (Fin D → ℂ) → ℝ) (z w : Fin D → ℂ) (ζ a b : ℂ) :
    Hc φ z w ζ a b = fderiv ℝ (fderiv ℝ φ) (z + ζ • w) (a • w) (b • w) := by sorry
