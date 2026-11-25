-- Prove2me | Theorems.Thm_ReciprocityTheory_P1_isHausdorff_comap_constantCoeff
-- name    : ReciprocityTheory.P1.isHausdorff_comap_constantCoeff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:24.538571+00:00
-- url     : https://prove2.me/theorems/76871870-2704-4975-b965-4290e86c34ce
-- title:
--   P1: is Hausdorff comap constant Coeff
-- statement:
--   The P1 construction uses the is Hausdorff comap constant Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdicCompleteness/IsAdicCompleteComapConstantCoeff.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdicCompleteness/IsAdicCompleteComapConstantCoeff.lean#L67-L75

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

theorem ReciprocityTheory.P1.isHausdorff_comap_constantCoeff [IsHausdorff I A] :
    IsHausdorff (I.comap (constantCoeff (R := A))) A⟦X⟧ := by sorry
