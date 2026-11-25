-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_pow_le_520c32532769
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_pow_le_520c32532769
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:04:41.577906+00:00
-- url     : https://prove2.me/theorems/d14308df-a16a-5d24-8dac-a070c602b90d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ideal Chart pow le 520c32532769: P2 M Ground Theory Heights  Heights Kleiman ideal Chart pow le 520c32532769
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ideal Chart pow le 520c32532769 construction uses the P2 M Ground Theory Heights  Heights Kleiman ideal Chart pow le 520c32532769 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L62-L68

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_pow_le_520c32532769 (P : Ideal (Poly k N)) (I : Chart x) (n : ℕ) :
    idealChart P I ^ n ≤ idealChart (x := x) (P ^ n) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«idealChart_pow_le» := P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_pow_le_520c32532769
