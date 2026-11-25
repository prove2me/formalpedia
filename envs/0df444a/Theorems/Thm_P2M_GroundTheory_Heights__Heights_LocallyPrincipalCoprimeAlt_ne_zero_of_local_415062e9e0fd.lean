-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_ne_zero_of_local_415062e9e0fd
-- name    : P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_ne_zero_of_local_415062e9e0fd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:46.941399+00:00
-- url     : https://prove2.me/theorems/abd84ece-dea3-44f1-a3cb-bc8c158e43f9
-- title:
--   P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt ne zero of local 415062e9e0fd: P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt ne zero of local 415062e9e0fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt ne zero of local 415062e9e0fd construction uses the P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt ne zero of local 415062e9e0fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLocallyPrincipalCoprime.lean#L50-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLocallyPrincipalCoprime.lean#L50-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLocallyPrincipalCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
variable {L : Type} [Field L]

theorem P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_ne_zero_of_local_415062e9e0fd {B : Subring L} {M : AddSubgroup L} {ι : Type} {a : ι → L} {m : Ideal B} {i : ι}
    (hi : ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i) (hM : M ≠ ⊥) : a i ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocallyPrincipalCoprimeAlt».«ne_zero_of_local» := P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_ne_zero_of_local_415062e9e0fd
