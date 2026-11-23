-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrableOn_radJ
-- name    : ReciprocityTheory.MultiplicativeHeights.integrableOn_radJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:54.552091+00:00
-- url     : https://prove2.me/theorems/20a144ed-e867-4d1c-aba7-464fdccc8e4a
-- title:
--   Multiplicative Heights: integrable On rad J
-- statement:
--   The Multiplicative Heights construction uses the integrable On rad J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreA.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreA.lean#L13-L17

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

theorem ReciprocityTheory.MultiplicativeHeights.integrableOn_radJ (k : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ k * exp (-r ^ 2)) (Ioi 0) := by sorry
