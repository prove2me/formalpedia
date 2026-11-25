-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FramePlaneGraph_dim_sup_span_lt_659941234b1e
-- name    : P2M_GroundTheory_Heights__Heights_FramePlaneGraph_dim_sup_span_lt_659941234b1e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:59.386318+00:00
-- url     : https://prove2.me/theorems/244ccad9-7179-4a50-99c3-92ea475a1827
-- title:
--   P2 M Ground Theory Heights  Heights Frame Plane Graph dim sup span lt 659941234b1e: P2 M Ground Theory Heights  Heights Frame Plane Graph dim sup span lt 659941234b1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Frame Plane Graph dim sup span lt 659941234b1e construction uses the P2 M Ground Theory Heights  Heights Frame Plane Graph dim sup span lt 659941234b1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFramePlaneGraph.lean#L37-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFramePlaneGraph.lean#L37-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFramePlaneGraph
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
noncomputable section
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_FramePlaneGraph_dim_sup_span_lt_659941234b1e {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) {q : MvPolynomial (Fin n) ℂ} (hq : q ∉ J) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {q})) < d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FramePlaneGraph».«dim_sup_span_lt» := P2M_GroundTheory_Heights__Heights_FramePlaneGraph_dim_sup_span_lt_659941234b1e
