-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_X_8037db39b46c
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_X_8037db39b46c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:56:01.983929+00:00
-- url     : https://prove2.me/theorems/63fc99b4-2356-498e-a292-828caabbc6fe
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport X 8037db39b46c: P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport X 8037db39b46c
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport X 8037db39b46c construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport X 8037db39b46c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L13-L15

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

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_X_8037db39b46c (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (p : Fin f × Fin N) :
    restTransport f j k N e (X p) = X (p.1, e p.2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportLast».«transport_X» := P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_X_8037db39b46c
