-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_mem_of_map_mem_a634e76c1bc9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_mem_of_map_mem_a634e76c1bc9
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:26:53.010107+00:00
-- url     : https://prove2.me/theorems/a57862f1-439b-4f26-9e21-f80f41a73429
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact mem of map mem a634e76c1bc9: P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact mem of map mem a634e76c1bc9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact mem of map mem a634e76c1bc9 construction uses the P2 M Ground Theory Heights  Heights Kleiman Deg Loc Exact mem of map mem a634e76c1bc9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDegLocExact.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDegLocExact.lean#L32-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDegLocExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.DegLocExact

theorem P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_mem_of_map_mem_a634e76c1bc9 {ι R A B : Type*} [DecidableEq ι] [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] (φ : A → B) (h0 : φ 0 = 0)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hφ : ∀ i a, a ∈ 𝒜 i → φ a ∈ ℬ i)
    (hinj : Function.Injective φ) {a : A} {k : ι} (ha : φ a ∈ ℬ k) : a ∈ 𝒜 k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«DegLocExact».«mem_of_map_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_DegLocExact_mem_of_map_mem_a634e76c1bc9
