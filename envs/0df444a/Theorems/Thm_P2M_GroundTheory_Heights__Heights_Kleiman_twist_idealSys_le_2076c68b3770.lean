-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_le_2076c68b3770
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_le_2076c68b3770
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:11:32.953226+00:00
-- url     : https://prove2.me/theorems/bb1cd359-c577-467f-8616-34479771ddf5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys le 2076c68b3770: P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys le 2076c68b3770
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys le 2076c68b3770 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys le 2076c68b3770 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L70-L75

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_le_2076c68b3770 (F : SubSystem k x Ω) (pp : Ideal (Poly k N)) (I : Chart x) :
    (F.twist (idealSys x pp)).sub I ≤ idealChart pp I • F.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twist_idealSys_le» := P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_le_2076c68b3770
