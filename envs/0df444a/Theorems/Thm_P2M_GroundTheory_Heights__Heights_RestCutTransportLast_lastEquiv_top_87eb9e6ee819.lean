-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_lastEquiv_top_87eb9e6ee819
-- name    : P2M_GroundTheory_Heights__Heights_RestCutTransportLast_lastEquiv_top_87eb9e6ee819
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:57:13.402429+00:00
-- url     : https://prove2.me/theorems/48466bba-5c2c-4424-9ca7-1be7060f4a24
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Transport Last last Equiv top 87eb9e6ee819: P2 M Ground Theory Heights  Heights Rest Cut Transport Last last Equiv top 87eb9e6ee819
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Transport Last last Equiv top 87eb9e6ee819 construction uses the P2 M Ground Theory Heights  Heights Rest Cut Transport Last last Equiv top 87eb9e6ee819 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutTransportLast.lean#L21-L24

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

theorem P2M_GroundTheory_Heights__Heights_RestCutTransportLast_lastEquiv_top_87eb9e6ee819 (j k : ℕ) (i : Fin j) (h : (i : ℕ) < k + j) :
    restLastEquiv j k ⟨i, h⟩ = Sum.inl i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutTransportLast».«lastEquiv_top» := P2M_GroundTheory_Heights__Heights_RestCutTransportLast_lastEquiv_top_87eb9e6ee819
