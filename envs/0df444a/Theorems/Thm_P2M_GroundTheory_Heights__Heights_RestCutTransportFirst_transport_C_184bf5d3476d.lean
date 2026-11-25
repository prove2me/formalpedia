-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_C_184bf5d3476d
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_C_184bf5d3476d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:57:18.163131+00:00
-- url     : https://prove2.me/theorems/19e3a16c-cc3f-4570-b490-b8ab6decc1b3
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport First transport C 184bf5d3476d: P2 M Ground Theory Heights  Heights Rest Cut Transport First transport C 184bf5d3476d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport First transport C 184bf5d3476d construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport First transport C 184bf5d3476d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportFirst.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportFirst.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportFirst
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
open GroundTheory.Heights₂.Heights.RestCutTransportFirst

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_C_184bf5d3476d (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (c : ℚ) :
    restTransport f j k N e (C c) = C (c : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportFirst».«transport_C» := P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_C_184bf5d3476d
