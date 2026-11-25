-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_fib_c12080988bb1
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_fib_c12080988bb1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:57:13.910175+00:00
-- url     : https://prove2.me/theorems/7991deb9-75f1-4c7c-97cb-a16aa49aaba2
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport First transport fib c12080988bb1: P2 M Ground Theory Heights  Heights Rest Cut Transport First transport fib c12080988bb1
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport First transport fib c12080988bb1 construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport First transport fib c12080988bb1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportFirst.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportFirst.lean#L46-L51

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

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_fib_c12080988bb1 (f j k : ℕ) (hjk : j < k) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.fibreClass f j k .first) =
      fibre f j k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportFirst».«transport_fib» := P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_fib_c12080988bb1
