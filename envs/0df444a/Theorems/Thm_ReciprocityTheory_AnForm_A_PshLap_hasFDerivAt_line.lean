-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_hasFDerivAt_line
-- name    : ReciprocityTheory.AnForm.A.PshLap.hasFDerivAt_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:46.337656+00:00
-- url     : https://prove2.me/theorems/5a2c7845-75a0-4b01-a383-2d93df3a11ae
-- title:
--   Psh Lap: has FDeriv At line
-- statement:
--   The Psh Lap construction uses the has FDeriv At line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L33-L35

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

theorem ReciprocityTheory.AnForm.A.PshLap.hasFDerivAt_line (z w : Fin D → ℂ) (ζ : ℂ) :
    HasFDerivAt (fun ζ : ℂ => z + ζ • w) (L0 w) ζ := by sorry
