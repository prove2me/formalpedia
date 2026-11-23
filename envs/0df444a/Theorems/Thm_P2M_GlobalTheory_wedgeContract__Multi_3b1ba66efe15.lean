-- Prove2me | Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- name    : P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:18.438308+00:00
-- url     : https://prove2.me/theorems/47572452-580c-40e1-9459-dfa3719c525e
-- title:
--   P2 M Global Theory wedge Contract  Multi 3b1ba66efe15: P2 M Global Theory wedge Contract  Multi 3b1ba66efe15
-- statement:
--   The P2 M Global Theory wedge Contract  Multi 3b1ba66efe15 construction uses the P2 M Global Theory wedge Contract  Multi 3b1ba66efe15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L202-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L202-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable (A : Type*) {B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] {D : ℕ}
variable {A} {L : Type*} [AddCommGroup L] [Module A L]

theorem P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15 (φ : Fin D → L →ₗ[A] B) (v : Fin D → L) :
    wedgeContract φ (exteriorPower.ιMulti A D v) = (Matrix.of fun j k => φ k (v j)).det := by sorry

alias «GlobalTheory».«wedgeContract_ιMulti» := P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
