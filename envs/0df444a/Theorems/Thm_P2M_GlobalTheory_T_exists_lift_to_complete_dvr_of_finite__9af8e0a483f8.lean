-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_lift_to_complete_dvr_of_finite__9af8e0a483f8
-- name    : P2M_GlobalTheory_T_exists_lift_to_complete_dvr_of_finite__9af8e0a483f8
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:32.852681+00:00
-- url     : https://prove2.me/theorems/8989150d-3c5e-4b85-999e-92ca084ff951
-- title:
--   P2 M Global Theory T exists lift to complete dvr of finite  9af8e0a483f8: P2 M Global Theory T exists lift to complete dvr of finite  9af8e0a483f8
-- statement:
--   The P2 M Global Theory T exists lift to complete dvr of finite  9af8e0a483f8 construction uses the P2 M Global Theory T exists lift to complete dvr of finite  9af8e0a483f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftToCompleteDvrOfFiniteStatement.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftToCompleteDvrOfFiniteStatement.lean#L7-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftToCompleteDvrOfFinite
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_IsLocalRingOfComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftToCompleteDvrOfFiniteStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_lift_to_complete_dvr_of_finite__9af8e0a483f8 : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R], Function.Injective (algebraMap A R) →
    Module.Finite A R → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ρ : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ ρ.comp (algebraMap A R) = f.comp h := by sorry

alias «GlobalTheory».«T».«exists_lift_to_complete_dvr_of_finite'» := P2M_GlobalTheory_T_exists_lift_to_complete_dvr_of_finite__9af8e0a483f8
