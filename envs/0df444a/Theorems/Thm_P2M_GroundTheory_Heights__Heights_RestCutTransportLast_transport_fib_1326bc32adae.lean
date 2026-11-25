-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_fib_1326bc32adae
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_fib_1326bc32adae
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:57:04.899117+00:00
-- url     : https://prove2.me/theorems/fd7b4f8d-ec11-4658-a888-2e58b1a1ccd2
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport fib 1326bc32adae: P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport fib 1326bc32adae
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport fib 1326bc32adae construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport fib 1326bc32adae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L52-L56

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

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_fib_1326bc32adae (f j k : ℕ) (hk : k ≤ j) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.fibreClass f k j .last) =
      fibre f j k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportLast».«transport_fib» := P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_fib_1326bc32adae
