-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_map_vandermondeOf_f16575da4a7f
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_map_vandermondeOf_f16575da4a7f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:50.499173+00:00
-- url     : https://prove2.me/theorems/a5c8024a-9036-4765-8351-23f745f2791b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport First map vandermonde Of f16575da4a7f: P2 M Ground Theory Heights  Heights Rest Cut Transport First map vandermonde Of f16575da4a7f
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport First map vandermonde Of f16575da4a7f construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport First map vandermonde Of f16575da4a7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportFirst.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportFirst.lean#L13-L15

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

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_map_vandermondeOf_f16575da4a7f {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ}
    (v : Fin m → R) : φ (RestTerms.vandermondeOf v) = RestTerms.vandermondeOf (fun i => φ (v i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportFirst».«map_vandermondeOf» := P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_map_vandermondeOf_f16575da4a7f
