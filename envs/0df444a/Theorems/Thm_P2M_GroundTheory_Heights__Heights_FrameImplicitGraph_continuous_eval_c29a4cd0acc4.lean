-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_continuous_eval_c29a4cd0acc4
-- name    : P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_continuous_eval_c29a4cd0acc4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:01.626925+00:00
-- url     : https://prove2.me/theorems/cbc0e2e0-46d3-456e-aaa5-74f8f6451b51
-- title:
--   P2 M Ground Theory Heights  Heights Frame Implicit Graph continuous eval c29a4cd0acc4: P2 M Ground Theory Heights  Heights Frame Implicit Graph continuous eval c29a4cd0acc4
-- statement:
--   The P2 M Ground Theory Heights  Heights Frame Implicit Graph continuous eval c29a4cd0acc4 construction uses the P2 M Ground Theory Heights  Heights Frame Implicit Graph continuous eval c29a4cd0acc4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameImplicitGraph.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameImplicitGraph.lean#L106-L108

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameImplicitGraph
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HasStrictFDerivAtEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
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
open GroundTheory.Heights₂.Heights.FrameImplicitGraph
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_continuous_eval_c29a4cd0acc4 (p : MvPolynomial (Fin n) ℂ) :
    Continuous fun y : EuclideanSpace ℂ (Fin n) => eval (fun i => y i) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FrameImplicitGraph».«continuous_eval» := P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_continuous_eval_c29a4cd0acc4
