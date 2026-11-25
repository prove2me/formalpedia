-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_map_vandermondeOf_0c093407b9f2
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportLast_map_vandermondeOf_0c093407b9f2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:55.886995+00:00
-- url     : https://prove2.me/theorems/5bb12495-014a-5831-9e1f-b9c396ca8775
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport Last map vandermonde Of 0c093407b9f2: P2 M Ground Theory Heights  Heights Rest Cut Transport Last map vandermonde Of 0c093407b9f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport Last map vandermonde Of 0c093407b9f2 construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport Last map vandermonde Of 0c093407b9f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L43-L45

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

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportLast_map_vandermondeOf_0c093407b9f2 {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) {m : ℕ}
    (v : Fin m → R) : g (RestTerms.vandermondeOf v) = RestTerms.vandermondeOf fun i => g (v i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportLast».«map_vandermondeOf» := P2M_GroundTheory_Heights__Heights_RestCutTransportLast_map_vandermondeOf_0c093407b9f2
