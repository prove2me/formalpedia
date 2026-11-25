-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_lastEquiv_bottom_671ead235411
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportLast_lastEquiv_bottom_671ead235411
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:55.86342+00:00
-- url     : https://prove2.me/theorems/4d9a3bd6-22bb-5717-bcd0-eb0d49590b37
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport Last last Equiv bottom 671ead235411: P2 M Ground Theory Heights  Heights Rest Cut Transport Last last Equiv bottom 671ead235411
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport Last last Equiv bottom 671ead235411 construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport Last last Equiv bottom 671ead235411 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L26-L29

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

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportLast_lastEquiv_bottom_671ead235411 (j k : ℕ) (i : Fin k) (h : j + (i : ℕ) < k + j) :
    restLastEquiv j k ⟨j + i, h⟩ = Sum.inr i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportLast».«lastEquiv_bottom» := P2M_GroundTheory_Heights__Heights_RestCutTransportLast_lastEquiv_bottom_671ead235411
