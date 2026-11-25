-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_line_hasFDerivAt_g
-- name    : ReciprocityTheory.AnForm.A.PshLap.line_hasFDerivAt_g
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:05:13.915316+00:00
-- url     : https://prove2.me/theorems/746514e9-acad-4e80-9372-eebb9fb58cca
-- title:
--   Psh Lap: line has FDeriv At g
-- statement:
--   The Psh Lap construction uses the line has FDeriv At g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L39-L45

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

theorem ReciprocityTheory.AnForm.A.PshLap.line_hasFDerivAt_g (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U) (z w : Fin D → ℂ) {ζ : ℂ}
    (hζ : z + ζ • w ∈ U) : HasFDerivAt (fun ζ : ℂ => φ (z + ζ • w)) (Gc φ z w ζ) ζ := by sorry
