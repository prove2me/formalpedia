-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_zRoot_27fb47ecf035
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_zRoot_27fb47ecf035
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:57:01.326576+00:00
-- url     : https://prove2.me/theorems/e0eca21a-f68c-4694-8f03-407841dc5657
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport First transport z Root 27fb47ecf035: P2 M Ground Theory Heights  Heights Rest Cut Transport First transport z Root 27fb47ecf035
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport First transport z Root 27fb47ecf035 construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport First transport z Root 27fb47ecf035 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportFirst.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportFirst.lean#L33-L38

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

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_zRoot_27fb47ecf035 (f j k : ℕ) (τ : Fin f) (i : Fin k) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.zRoot f j k .first τ i) =
      X (τ, Sum.inr i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportFirst».«transport_zRoot» := P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_zRoot_27fb47ecf035
