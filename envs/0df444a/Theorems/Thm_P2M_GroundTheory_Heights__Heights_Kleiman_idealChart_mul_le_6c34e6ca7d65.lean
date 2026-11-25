-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_mul_le_6c34e6ca7d65
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_mul_le_6c34e6ca7d65
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:36.901098+00:00
-- url     : https://prove2.me/theorems/99926b4b-ae4c-5e96-b372-aed19da06114
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ideal Chart mul le 6c34e6ca7d65: P2 M Ground Theory Heights  Heights Kleiman ideal Chart mul le 6c34e6ca7d65
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ideal Chart mul le 6c34e6ca7d65 construction uses the P2 M Ground Theory Heights  Heights Kleiman ideal Chart mul le 6c34e6ca7d65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L41-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnW
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThree
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_mul_le_6c34e6ca7d65 (J J' : Ideal (Poly k N)) (I : Chart x) :
    idealChart J I * idealChart J' I ≤ idealChart (x := x) (J * J') I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«idealChart_mul_le» := P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_mul_le_6c34e6ca7d65
