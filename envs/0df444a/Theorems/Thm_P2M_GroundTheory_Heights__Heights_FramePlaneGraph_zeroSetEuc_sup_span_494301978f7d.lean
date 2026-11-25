-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FramePlaneGraph_zeroSetEuc_sup_span_494301978f7d
-- name    : P2M_GroundTheory_Heights__Heights_FramePlaneGraph_zeroSetEuc_sup_span_494301978f7d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:00.90705+00:00
-- url     : https://prove2.me/theorems/0ff018d4-eb83-467e-8132-b91a39665b0f
-- title:
--   P2 M Ground Theory Heights  Heights Frame Plane Graph zero Set Euc sup span 494301978f7d: P2 M Ground Theory Heights  Heights Frame Plane Graph zero Set Euc sup span 494301978f7d
-- statement:
--   The P2 M Ground Theory Heights  Heights Frame Plane Graph zero Set Euc sup span 494301978f7d construction uses the P2 M Ground Theory Heights  Heights Frame Plane Graph zero Set Euc sup span 494301978f7d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFramePlaneGraph.lean#L12-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFramePlaneGraph.lean#L12-L25

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

theorem P2M_GroundTheory_Heights__Heights_FramePlaneGraph_zeroSetEuc_sup_span_494301978f7d {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (q : MvPolynomial (Fin n) ℂ) :
    zeroSetEuc (J ⊔ Ideal.span {q}) = zeroSetEuc J ∩ {z | eval (fun i => z i) q = 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FramePlaneGraph».«zeroSetEuc_sup_span» := P2M_GroundTheory_Heights__Heights_FramePlaneGraph_zeroSetEuc_sup_span_494301978f7d
