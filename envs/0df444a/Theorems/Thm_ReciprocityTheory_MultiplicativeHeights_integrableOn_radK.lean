-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrableOn_radK
-- name    : ReciprocityTheory.MultiplicativeHeights.integrableOn_radK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:07.507149+00:00
-- url     : https://prove2.me/theorems/ee07a6da-5111-4207-924f-50d667147f68
-- title:
--   Multiplicative Heights: integrable On rad K
-- statement:
--   The Multiplicative Heights construction uses the integrable On rad K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreA.lean#L35-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreA.lean#L35-L60

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

theorem ReciprocityTheory.MultiplicativeHeights.integrableOn_radK {k : ℕ} (hk : 1 ≤ k) :
    IntegrableOn (fun r : ℝ => r ^ k * log r * exp (-r ^ 2)) (Ioi 0) := by sorry
