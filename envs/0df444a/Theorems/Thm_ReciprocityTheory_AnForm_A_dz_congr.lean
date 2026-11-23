-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_dz_congr
-- name    : ReciprocityTheory.AnForm.A.dz_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:54.225721+00:00
-- url     : https://prove2.me/theorems/fadbef98-3b90-4d27-8c8f-dc9e5a4fecd4
-- title:
--   A: dz congr
-- statement:
--   The A construction uses the dz congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L129-L132

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
variable {D : ℕ} {j : Fin D} {f g : (Fin D → ℂ) → ℂ} {z : Fin D → ℂ}

theorem ReciprocityTheory.AnForm.A.dz_congr (h : f =ᶠ[𝓝 z] g) : dz j f z = dz j g z := by sorry
