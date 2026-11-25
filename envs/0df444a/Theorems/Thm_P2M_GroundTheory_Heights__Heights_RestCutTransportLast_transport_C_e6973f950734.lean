-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_C_e6973f950734
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_C_e6973f950734
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:52.008299+00:00
-- url     : https://prove2.me/theorems/412d15ed-398d-56db-a35f-3abc9629b2ad
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport C e6973f950734: P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport C e6973f950734
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport C e6973f950734 construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport Last transport C e6973f950734 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L17-L19

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

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_C_e6973f950734 (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (c : ℚ) :
    restTransport f j k N e (C c) = C (c : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportLast».«transport_C» := P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_C_e6973f950734
