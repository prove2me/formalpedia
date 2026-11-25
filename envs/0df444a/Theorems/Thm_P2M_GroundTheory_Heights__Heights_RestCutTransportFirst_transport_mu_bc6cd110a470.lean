-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_mu_bc6cd110a470
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_mu_bc6cd110a470
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:44.283365+00:00
-- url     : https://prove2.me/theorems/b39c4a1b-8c3c-5d18-99a0-4e252db5f723
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport First transport mu bc6cd110a470: P2 M Ground Theory Heights  Heights Rest Cut Transport First transport mu bc6cd110a470
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport First transport mu bc6cd110a470 construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport First transport mu bc6cd110a470 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportFirst.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportFirst.lean#L40-L44

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

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_mu_bc6cd110a470 (f j k : ℕ) (hjk : j < k) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.smallBlockMu f j k .first) =
      smallMu f j k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportFirst».«transport_mu» := P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_mu_bc6cd110a470
