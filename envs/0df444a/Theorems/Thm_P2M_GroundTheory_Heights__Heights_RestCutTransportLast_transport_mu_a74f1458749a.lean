-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_mu_a74f1458749a
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_mu_a74f1458749a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:57:00.566674+00:00
-- url     : https://prove2.me/theorems/4e7e32b6-d84f-4255-98e4-a10ed5aa1961
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport mu a74f1458749a: P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport mu a74f1458749a
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport mu a74f1458749a construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport mu a74f1458749a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L47-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportLast
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
open GroundTheory.Heights₂.Heights.RestCutTransportLast

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_mu_a74f1458749a (f j k : ℕ) (hk : k ≤ j) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.smallBlockMu f k j .last) =
      smallMu f j k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportLast».«transport_mu» := P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_mu_a74f1458749a
