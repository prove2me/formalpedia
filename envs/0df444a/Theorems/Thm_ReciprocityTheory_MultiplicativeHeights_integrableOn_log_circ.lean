-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrableOn_log_circ
-- name    : ReciprocityTheory.MultiplicativeHeights.integrableOn_log_circ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:52.805807+00:00
-- url     : https://prove2.me/theorems/f1e7c2a4-8efd-4c3c-9276-9409941da8d9
-- title:
--   Multiplicative Heights: integrable On log circ
-- statement:
--   The Multiplicative Heights construction uses the integrable On log circ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanA.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanA.lean#L21-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
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
open MeasureTheory Polynomial Real

theorem ReciprocityTheory.MultiplicativeHeights.integrableOn_log_circ (p : ℂ[X]) :
    IntegrableOn (fun t => Real.log ‖p.eval (circPt t)‖) (Set.Ioc (0 : ℝ) 1) := by sorry
