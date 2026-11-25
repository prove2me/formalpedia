-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_mem_span_of_local_4d6d182557f9
-- name    : P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_mem_span_of_local_4d6d182557f9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:02.345494+00:00
-- url     : https://prove2.me/theorems/18e13a7d-a64e-4ec3-b2a3-f13efef9ce75
-- title:
--   P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt mem span of local 4d6d182557f9: P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt mem span of local 4d6d182557f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt mem span of local 4d6d182557f9 construction uses the P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt mem span of local 4d6d182557f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLocallyPrincipalCoprime.lean#L31-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLocallyPrincipalCoprime.lean#L31-L48

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

theorem P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_mem_span_of_local_4d6d182557f9 {B : Subring L} {M : AddSubgroup L} {ι : Type} {a : ι → L}
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i)
    {z : L} (hz : z ∈ M) : z ∈ Submodule.span B (Set.range a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocallyPrincipalCoprimeAlt».«mem_span_of_local» := P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_mem_span_of_local_4d6d182557f9
