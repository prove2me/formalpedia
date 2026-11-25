-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_yRoot_fbd963f505e6
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_yRoot_fbd963f505e6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:56:20.060589+00:00
-- url     : https://prove2.me/theorems/a7a313bd-fb7d-4bb4-8a8b-4df9f20b97bf
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport y Root fbd963f505e6: P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport y Root fbd963f505e6
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport y Root fbd963f505e6 construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport y Root fbd963f505e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L31-L36

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

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_yRoot_fbd963f505e6 (f j k : ℕ) (τ : Fin f) (i : Fin k) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.yRoot f k j .last τ i) =
      X (τ, Sum.inr i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportLast».«transport_yRoot» := P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_yRoot_fbd963f505e6
