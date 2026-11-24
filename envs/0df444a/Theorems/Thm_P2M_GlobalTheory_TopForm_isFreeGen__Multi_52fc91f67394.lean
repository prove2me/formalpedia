-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TopForm_isFreeGen__Multi_52fc91f67394
-- name    : P2M_GlobalTheory_TopForm_isFreeGen__Multi_52fc91f67394
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:09.148663+00:00
-- url     : https://prove2.me/theorems/ac86507d-bf85-49b7-bd50-03862b17d022
-- title:
--   P2 M Global Theory Top Form is Free Gen  Multi 52fc91f67394: P2 M Global Theory Top Form is Free Gen  Multi 52fc91f67394
-- statement:
--   The P2 M Global Theory Top Form is Free Gen  Multi 52fc91f67394 construction uses the P2 M Global Theory Top Form is Free Gen  Multi 52fc91f67394 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L123-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L123-L135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

theorem P2M_GlobalTheory_TopForm_isFreeGen__Multi_52fc91f67394 {D : ℕ} (b : Module.Basis (Fin D) A M) :
    IsFreeGen A (exteriorPower.ιMulti A D b) := by sorry

alias «GlobalTheory».«TopForm».«isFreeGen_ιMulti» := P2M_GlobalTheory_TopForm_isFreeGen__Multi_52fc91f67394
