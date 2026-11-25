-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_radRatio_odd
-- name    : ReciprocityTheory.MultiplicativeHeights.radRatio_odd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:43.374965+00:00
-- url     : https://prove2.me/theorems/25903342-5a7b-4bb8-99cd-b8fffa67bbbc
-- title:
--   Multiplicative Heights: rad Ratio odd
-- statement:
--   The Multiplicative Heights construction uses the rad Ratio odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreA.lean#L151-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreA.lean#L151-L160

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Set Real Filter Topology

theorem ReciprocityTheory.MultiplicativeHeights.radRatio_odd (m : ℕ) :
    radK (2 * m + 1) / radJ (2 * m + 1) = radK 1 / radJ 1 + (harmonic m : ℝ) / 2 := by sorry
