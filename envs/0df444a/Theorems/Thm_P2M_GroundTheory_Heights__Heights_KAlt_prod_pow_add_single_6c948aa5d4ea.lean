-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_prod_pow_add_single_6c948aa5d4ea
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_prod_pow_add_single_6c948aa5d4ea
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:44.87725+00:00
-- url     : https://prove2.me/theorems/84230503-326c-5d80-bf2a-6265ba1ac145
-- title:
--   P2 M Ground Theory Heights  Heights KAlt prod pow add single 6c948aa5d4ea: P2 M Ground Theory Heights  Heights KAlt prod pow add single 6c948aa5d4ea
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt prod pow add single 6c948aa5d4ea construction uses the P2 M Ground Theory Heights  Heights KAlt prod pow add single 6c948aa5d4ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltRow.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltRow.lean#L11-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltRow
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
open MvPolynomial
open GroundTheory.Heights₂.Heights.KAlt

theorem P2M_GroundTheory_Heights__Heights_KAlt_prod_pow_add_single_6c948aa5d4ea {r : ℕ} (q : ℕ) (μ : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    ∏ i', (X (σ i') : MvPolynomial (Fin r) ℚ) ^ ((μ + Pi.single i q : Fin r → ℕ) i') =
      X (σ i) ^ q * ∏ i', (X (σ i') : MvPolynomial (Fin r) ℚ) ^ μ i' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«prod_pow_add_single» := P2M_GroundTheory_Heights__Heights_KAlt_prod_pow_add_single_6c948aa5d4ea
