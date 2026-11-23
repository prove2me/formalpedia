-- Prove2me | Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
-- name    : P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:19.73879+00:00
-- url     : https://prove2.me/theorems/9ac6b0a7-6024-46cd-99d7-994b970945ed
-- title:
--   P2 M Global Theory exterior Power Map Over  Multi e236a206a98b: P2 M Global Theory exterior Power Map Over  Multi e236a206a98b
-- statement:
--   The P2 M Global Theory exterior Power Map Over  Multi e236a206a98b construction uses the P2 M Global Theory exterior Power Map Over  Multi e236a206a98b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L192-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L192-L195

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

theorem P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b (φ : L →ₗ[A] M) (v : Fin D → L) :
    exteriorPowerMapOver B D φ (exteriorPower.ιMulti A D v)
      = exteriorPower.ιMulti B D (fun k => φ (v k)) := by sorry

alias «GlobalTheory».«exteriorPowerMapOver_ιMulti» := P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
