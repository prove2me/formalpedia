-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_hasStrictFDerivAt_eval_bed54b8aac66
-- name    : P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_hasStrictFDerivAt_eval_bed54b8aac66
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:47.753347+00:00
-- url     : https://prove2.me/theorems/5f49c9be-fe03-4700-8a12-e1304c90b07d
-- title:
--   P2 M Ground Theory Heights  Heights Frame Implicit Graph has Strict FDeriv At eval bed54b8aac66: P2 M Ground Theory Heights  Heights Frame Implicit Graph has Strict FDeriv At eval bed54b8aac66
-- statement:
--   The P2 M Ground Theory Heights  Heights Frame Implicit Graph has Strict FDeriv At eval bed54b8aac66 construction uses the P2 M Ground Theory Heights  Heights Frame Implicit Graph has Strict FDeriv At eval bed54b8aac66 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameImplicitGraph.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameImplicitGraph.lean#L24-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameImplicitGraph
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HasStrictFDerivAtEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
import Theorems.Thm_UpperTheory_Reformulated_B_Qi29_hasStrictFDerivAt_eval

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

theorem P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_hasStrictFDerivAt_eval_bed54b8aac66 (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    HasStrictFDerivAt (fun y : EuclideanSpace ℂ (Fin n) => eval (fun i => y i) p) (polyDeriv p x) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FrameImplicitGraph».«hasStrictFDerivAt_eval» := P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_hasStrictFDerivAt_eval_bed54b8aac66
