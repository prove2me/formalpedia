-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TildeFinite_proof_8f258b787eb6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TildeFinite_proof_8f258b787eb6
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:30:39.657287+00:00
-- url     : https://prove2.me/theorems/90ec297e-db0d-5ba6-a11b-f89a57c7443c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Tilde Finite proof 8f258b787eb6: P2 M Ground Theory Heights  Heights Kleiman Tilde Finite proof 8f258b787eb6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Tilde Finite proof 8f258b787eb6 construction uses the P2 M Ground Theory Heights  Heights Kleiman Tilde Finite proof 8f258b787eb6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L248-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L248-L259

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Transport_proof_0f907ba81f5e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TildeTail_proof_fa6492dcadb7

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TildeFinite_proof_8f258b787eb6 (h : SerreFinite.Statement.{u, w}) : TildeFinite.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TildeFinite».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_TildeFinite_proof_8f258b787eb6
