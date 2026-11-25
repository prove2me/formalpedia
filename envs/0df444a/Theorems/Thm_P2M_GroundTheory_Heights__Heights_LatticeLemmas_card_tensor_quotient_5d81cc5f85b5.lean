-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_tensor_quotient_5d81cc5f85b5
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_tensor_quotient_5d81cc5f85b5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:51.300828+00:00
-- url     : https://prove2.me/theorems/837bccb1-8d33-47ce-890d-a545fbd74498
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas card tensor quotient 5d81cc5f85b5: P2 M Ground Theory Heights  Heights Lattice Lemmas card tensor quotient 5d81cc5f85b5
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas card tensor quotient 5d81cc5f85b5 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas card tensor quotient 5d81cc5f85b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/BaseChangeIndex.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/BaseChangeIndex.lean#L15-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_BaseChangeIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField TensorProduct
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_tensor_quotient_5d81cc5f85b5 (I : Ideal (𝓞 K)) :
    Nat.card (𝓞 L ⊗[𝓞 K] (𝓞 K ⧸ I)) = Nat.card (𝓞 K ⧸ I) ^ Module.finrank K L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«card_tensor_quotient» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_tensor_quotient_5d81cc5f85b5
