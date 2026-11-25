-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsChowFormCycle_C_mul_f39b13a892e3
-- name    : P2M_GroundTheory_Heights__Heights_IsChowFormCycle_C_mul_f39b13a892e3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:44:09.494089+00:00
-- url     : https://prove2.me/theorems/2b138eaa-18ee-4c69-85fb-b04d0b32aa6b
-- title:
--   P2 M Ground Theory Heights  Heights Is Chow Form Cycle C mul f39b13a892e3: P2 M Ground Theory Heights  Heights Is Chow Form Cycle C mul f39b13a892e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Chow Form Cycle C mul f39b13a892e3 construction uses the P2 M Ground Theory Heights  Heights Is Chow Form Cycle C mul f39b13a892e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PCycleSectionChow.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PCycleSectionChow.lean#L15-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PCycleSectionChow
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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IsChowFormCycle_C_mul_f39b13a892e3 {F : Type*} [Field F] {n k : ℕ} {Z : ProjCycle F n}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowFormCycle Z k f) {c : F} (hc : c ≠ 0) :
    IsChowFormCycle Z k (C c * f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsChowFormCycle».«C_mul» := P2M_GroundTheory_Heights__Heights_IsChowFormCycle_C_mul_f39b13a892e3
