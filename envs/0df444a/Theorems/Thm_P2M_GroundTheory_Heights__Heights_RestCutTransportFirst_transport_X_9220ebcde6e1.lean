-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_X_9220ebcde6e1
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_X_9220ebcde6e1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:56:41.846378+00:00
-- url     : https://prove2.me/theorems/33308920-e6e0-59df-b624-00a07a60095f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport First transport X 9220ebcde6e1: P2 M Ground Theory Heights  Heights Rest Cut Transport First transport X 9220ebcde6e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport First transport X 9220ebcde6e1 construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport First transport X 9220ebcde6e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportFirst.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportFirst.lean#L17-L19

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

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_X_9220ebcde6e1 (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (p : Fin f × Fin N) :
    restTransport f j k N e (X p) = X (p.1, e p.2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportFirst».«transport_X» := P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_X_9220ebcde6e1
