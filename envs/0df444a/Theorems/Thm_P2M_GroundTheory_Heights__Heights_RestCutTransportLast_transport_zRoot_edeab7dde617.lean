-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_zRoot_edeab7dde617
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_zRoot_edeab7dde617
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:18.751251+00:00
-- url     : https://prove2.me/theorems/0cd1eefc-585b-5e84-9788-8eb0417c79dc
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport z Root edeab7dde617: P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport z Root edeab7dde617
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport z Root edeab7dde617 construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport z Root edeab7dde617 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L38-L41

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

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_zRoot_edeab7dde617 (f j k : ℕ) (τ : Fin f) (i : Fin j) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.zRoot f k j .last τ i) =
      X (τ, Sum.inl i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportLast».«transport_zRoot» := P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_zRoot_edeab7dde617
