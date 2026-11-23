-- Prove2me | Theorems.Thm_ReciprocityTheory_P1_isAdicComplete_ps
-- name    : ReciprocityTheory.P1.isAdicComplete_ps
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:11.811435+00:00
-- url     : https://prove2.me/theorems/c2a48187-158b-4ab7-9e17-17001a6a8d02
-- title:
--   P1: is Adic Complete ps
-- statement:
--   The P1 construction uses the is Adic Complete ps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdicCompleteness/IsAdicCompleteComapConstantCoeff.lean#L102-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdicCompleteness/IsAdicCompleteComapConstantCoeff.lean#L102-L109

import Mathlib
import Definitions.Def_ReciprocityTheory_AdicCompleteness_IsAdicCompleteComapConstantCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open PowerSeries IsLocalRing
noncomputable section
open ReciprocityTheory ReciprocityTheory.P1

theorem ReciprocityTheory.P1.isAdicComplete_ps {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal R⟦X⟧) R⟦X⟧ := by sorry
