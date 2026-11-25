-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_leadingCoeff_nonneg_of_eventually_0ddfabcf76f5
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_leadingCoeff_nonneg_of_eventually_0ddfabcf76f5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:06.535649+00:00
-- url     : https://prove2.me/theorems/bc12816d-a4b6-43ec-81cd-f9cbd8ee5458
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich leading Coeff nonneg of eventually 0ddfabcf76f5: P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich leading Coeff nonneg
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich leading Coeff nonneg of eventually 0ddfabcf76f5 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich leading Coeff nonneg of eventually 0ddfabcf76f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPolySandwich.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPolySandwich.lean#L9-L22

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_leadingCoeff_nonneg_of_eventually_0ddfabcf76f5 (f : ℚ[X])
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f.eval (n : ℚ)) : 0 ≤ f.leadingCoeff := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«PolySandwich».«leadingCoeff_nonneg_of_eventually» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_leadingCoeff_nonneg_of_eventually_0ddfabcf76f5
