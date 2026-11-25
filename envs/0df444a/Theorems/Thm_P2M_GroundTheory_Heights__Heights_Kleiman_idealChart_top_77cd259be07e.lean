-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_top_77cd259be07e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_top_77cd259be07e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:57.247382+00:00
-- url     : https://prove2.me/theorems/47c997a6-f09d-5917-88e6-b13eddccc1be
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ideal Chart top 77cd259be07e: P2 M Ground Theory Heights  Heights Kleiman ideal Chart top 77cd259be07e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ideal Chart top 77cd259be07e construction uses the P2 M Ground Theory Heights  Heights Kleiman ideal Chart top 77cd259be07e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L47-L51

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_top_77cd259be07e (I : Chart x) : idealChart (x := x) (⊤ : Ideal (Poly k N)) I = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«idealChart_top» := P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_top_77cd259be07e
