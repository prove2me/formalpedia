-- Prove2me | Theorems.Thm_ReciprocityTheory_P1_isAdicComplete_comap_constantCoeff
-- name    : ReciprocityTheory.P1.isAdicComplete_comap_constantCoeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:10.316218+00:00
-- url     : https://prove2.me/theorems/155ef9cc-1a10-4a84-9ba3-f716f0644ff0
-- title:
--   P1: is Adic Complete comap constant Coeff
-- statement:
--   The P1 construction uses the is Adic Complete comap constant Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdicCompleteness/IsAdicCompleteComapConstantCoeff.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdicCompleteness/IsAdicCompleteComapConstantCoeff.lean#L96-L98

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
variable {A : Type*} [CommRing A] (I : Ideal A)

theorem ReciprocityTheory.P1.isAdicComplete_comap_constantCoeff [IsAdicComplete I A] :
    IsAdicComplete (I.comap (constantCoeff (R := A))) A⟦X⟧ := by sorry
