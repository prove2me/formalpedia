-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_pairing_single_4a952709d21e
-- name    : P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_pairing_single_4a952709d21e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:40.914719+00:00
-- url     : https://prove2.me/theorems/742d55f2-fd6f-4eeb-a8f4-92fb2e046287
-- title:
--   P2 M Ground Theory Heights  Heights Dual Embedding Bijective pairing single 4a952709d21e: P2 M Ground Theory Heights  Heights Dual Embedding Bijective pairing single 4a952709d21e
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Embedding Bijective pairing single 4a952709d21e construction uses the P2 M Ground Theory Heights  Heights Dual Embedding Bijective pairing single 4a952709d21e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualEmbBijective.lean#L52-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualEmbBijective.lean#L52-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualEmbBijective
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
open NumberField Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.DualEmbeddingBijective
variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_pairing_single_4a952709d21e (w : (K →+* ℂ) × Fin i → ℂ) (j : Fin i) (x : K) :
    pairing w (Pi.single j x) = ∑ σ : K →+* ℂ, w (σ, j) * σ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualEmbeddingBijective».«pairing_single» := P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_pairing_single_4a952709d21e
