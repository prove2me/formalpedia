-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_coeff_nonneg_of_eventually_f87525e47f89
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_coeff_nonneg_of_eventually_f87525e47f89
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:52.576072+00:00
-- url     : https://prove2.me/theorems/f0dc914a-5df5-4470-9b10-e549e81a4d51
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich coeff nonneg of eventually f87525e47f89: P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich coeff nonneg of eventually f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich coeff nonneg of eventually f87525e47f89 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich coeff nonneg of eventually f87525e47f89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPolySandwich.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPolySandwich.lean#L24-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolySandwich
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPolySandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial Filter

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_coeff_nonneg_of_eventually_f87525e47f89 (f : ℚ[X]) (E : ℕ) (hE : f.natDegree ≤ E)
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f.eval (n : ℚ)) : 0 ≤ f.coeff E := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«PolySandwich».«coeff_nonneg_of_eventually» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_coeff_nonneg_of_eventually_f87525e47f89
