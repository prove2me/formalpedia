-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_exists_local_mult_e9c2278c58f0
-- name    : P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_exists_local_mult_e9c2278c58f0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:04.58811+00:00
-- url     : https://prove2.me/theorems/ba50c1e8-df17-43d2-a166-cfb86251e6c1
-- title:
--   P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt exists local mult e9c2278c58f0: P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt exists local mult e9c2278c58f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt exists local mult e9c2278c58f0 construction uses the P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt exists local mult e9c2278c58f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLocallyPrincipalCoprime.lean#L62-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLocallyPrincipalCoprime.lean#L62-L96

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

theorem P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_exists_local_mult_e9c2278c58f0 {B : Subring L} {M : AddSubgroup L} {ι : Type} [Fintype ι] {a : ι → L}
    (haM : ∀ i, a i ∈ M)
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i)
    (hM : M ≠ ⊥) (m : Ideal B) (hm : m.IsMaximal) :
    ∃ (g : L) (i : ι), (∀ z ∈ M, g * z ∈ B) ∧ ∃ y : B, (y : L) = g * a i ∧ y ∉ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocallyPrincipalCoprimeAlt».«exists_local_mult» := P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_exists_local_mult_e9c2278c58f0
