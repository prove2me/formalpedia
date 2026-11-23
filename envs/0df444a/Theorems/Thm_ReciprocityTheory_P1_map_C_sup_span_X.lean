-- Prove2me | Theorems.Thm_ReciprocityTheory_P1_map_C_sup_span_X
-- name    : ReciprocityTheory.P1.map_C_sup_span_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:08.257194+00:00
-- url     : https://prove2.me/theorems/e7d45223-a4bd-462c-9a53-37ef568317d8
-- title:
--   P1: map C sup span X
-- statement:
--   The P1 construction uses the map C sup span X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdicCompleteness/IsAdicCompleteComapConstantCoeff.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdicCompleteness/IsAdicCompleteComapConstantCoeff.lean#L15-L27

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

theorem ReciprocityTheory.P1.map_C_sup_span_X :
    I.map (C : A →+* A⟦X⟧) ⊔ Ideal.span {X} = I.comap (constantCoeff (R := A)) := by sorry
