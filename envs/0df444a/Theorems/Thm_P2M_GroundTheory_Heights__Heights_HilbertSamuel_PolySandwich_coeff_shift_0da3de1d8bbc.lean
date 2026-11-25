-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_coeff_shift_0da3de1d8bbc
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_coeff_shift_0da3de1d8bbc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:50.881743+00:00
-- url     : https://prove2.me/theorems/6bdc0582-c170-5e3c-a4b7-50c40c0db449
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich coeff shift 0da3de1d8bbc: P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich coeff shift 0da3de1d8bbc
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich coeff shift 0da3de1d8bbc construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich coeff shift 0da3de1d8bbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPolySandwich.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPolySandwich.lean#L34-L44

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_coeff_shift_0da3de1d8bbc (p : ℚ[X]) (c : ℚ) (E : ℕ) (hE : p.natDegree ≤ E) :
    (p.comp (X + C c)).coeff E = p.coeff E := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«PolySandwich».«coeff_shift» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_coeff_shift_0da3de1d8bbc
