-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sgn_mul_self_cf0b42db396f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sgn_mul_self_cf0b42db396f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:23:25.544976+00:00
-- url     : https://prove2.me/theorems/3d6c37e0-c09d-4d9a-a519-4b4eccf2333d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sgn mul self cf0b42db396f: P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sgn mul self cf0b42db396f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sgn mul self cf0b42db396f construction uses the P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sgn mul self cf0b42db396f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L193-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L193-L195

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
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
open GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sgn_mul_self_cf0b42db396f {n : ℕ} (L : Finset (Fin n)) (j : Fin n) : Cech.sgn L j * Cech.sgn L j = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SurjectiveClosed».«sgn_mul_self» := P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sgn_mul_self_cf0b42db396f
