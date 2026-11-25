-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_plurisubharmonicIffLeviNonneg_holds
-- name    : ReciprocityTheory.AnForm.A.PshLap.plurisubharmonicIffLeviNonneg_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:12.41009+00:00
-- url     : https://prove2.me/theorems/872d3463-9162-4545-96e4-d0c84e24387e
-- title:
--   Psh Lap: plurisubharmonic Iff Levi Nonneg holds
-- statement:
--   The Psh Lap construction uses the plurisubharmonic Iff Levi Nonneg holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L68-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L68-L119

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

theorem ReciprocityTheory.AnForm.A.PshLap.plurisubharmonicIffLeviNonneg_holds : IsPsh_iff_isLeviPshStatement := by sorry
