-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_line_contOn_H
-- name    : ReciprocityTheory.AnForm.A.PshLap.line_contOn_H
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:04:59.369999+00:00
-- url     : https://prove2.me/theorems/e180839c-aeab-43d7-a9eb-103378347e4c
-- title:
--   Psh Lap: line cont On H
-- statement:
--   The Psh Lap construction uses the line cont On H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L54-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L54-L60

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

theorem ReciprocityTheory.AnForm.A.PshLap.line_contOn_H (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U) (z w : Fin D → ℂ) :
    ContinuousOn (Hc φ z w) {ζ : ℂ | z + ζ • w ∈ U} := by sorry
