-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_line_coord
-- name    : ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.line_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:12.110999+00:00
-- url     : https://prove2.me/theorems/0e481b90-0cb8-423f-b9c4-56be1c9251c1
-- title:
--   Plurisubharmonic Extension: line coord
-- statement:
--   The Plurisubharmonic Extension construction uses the line coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtB.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtB.lean#L47-L50

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
open ReciprocityTheory.AnForm.A
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.line_coord (x : Fin D → ℂ) (j i : Fin D) (ζ : ℂ) :
    (x + ζ • ej j) i = x i + if i = j then ζ else 0 := by sorry
