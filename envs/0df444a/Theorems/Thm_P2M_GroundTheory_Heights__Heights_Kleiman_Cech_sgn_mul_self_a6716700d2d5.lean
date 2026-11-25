-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_sgn_mul_self_a6716700d2d5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_sgn_mul_self_a6716700d2d5
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:54:16.727916+00:00
-- url     : https://prove2.me/theorems/b1669fa1-63cd-4cbd-8cf3-c8f84f1ebfec
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech sgn mul self a6716700d2d5: P2 M Ground Theory Heights  Heights Kleiman Cech sgn mul self a6716700d2d5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech sgn mul self a6716700d2d5 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech sgn mul self a6716700d2d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTail.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTail.lean#L26-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_sgn_mul_self_a6716700d2d5 {n : ℕ} (J : Finset (Fin n)) (j : Fin n) : Cech.sgn J j * Cech.sgn J j = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«sgn_mul_self» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_sgn_mul_self_a6716700d2d5
