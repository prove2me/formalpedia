-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_yRoot_95c46a98cd5a
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_yRoot_95c46a98cd5a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:56:33.391802+00:00
-- url     : https://prove2.me/theorems/f54252b6-0ff1-4886-901f-18b91cd095ad
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport First transport y Root 95c46a98cd5a: P2 M Ground Theory Heights  Heights Rest Cut Transport First transport y Root 95c46a98cd5a
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport First transport y Root 95c46a98cd5a construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport First transport y Root 95c46a98cd5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportFirst.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportFirst.lean#L25-L31

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

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_yRoot_95c46a98cd5a (f j k : ℕ) (τ : Fin f) (i : Fin j) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.yRoot f j k .first τ i) =
      -X (τ, Sum.inl i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportFirst».«transport_yRoot» := P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_yRoot_95c46a98cd5a
