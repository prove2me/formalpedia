-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_term_eq_8e0283e60fb9
-- name    : P2M_GroundTheory_Heights__Heights_logCardLength_term_eq_8e0283e60fb9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:17.890838+00:00
-- url     : https://prove2.me/theorems/43d04347-a919-4f3d-9c6f-eb796b750ed5
-- title:
--   P2 M Ground Theory Heights  Heights log Card Length term eq 8e0283e60fb9: P2 M Ground Theory Heights  Heights log Card Length term eq 8e0283e60fb9
-- statement:
--   The P2 M Ground Theory Heights  Heights log Card Length term eq 8e0283e60fb9 construction uses the P2 M Ground Theory Heights  Heights log Card Length term eq 8e0283e60fb9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLogCardLength.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLogCardLength.lean#L24-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLogCardLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLogCardLength
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
noncomputable section
open GroundTheory.Heights₂.Heights.logCardLength
open Module
variable (R : Type) [CommRing R]
variable {R}

theorem P2M_GroundTheory_Heights__Heights_logCardLength_term_eq_8e0283e60fb9 (N : Type) [AddCommGroup N] [Module R N] (m : Ideal R) [hm : m.IsMaximal] :
    term R N m = ((Module.length (Localization.AtPrime m)
      (LocalizedModule m.primeCompl N)).toNat : ℝ) * Real.log (Nat.card (R ⧸ m)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«logCardLength».«term_eq» := P2M_GroundTheory_Heights__Heights_logCardLength_term_eq_8e0283e60fb9
