-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_phiDeriv_injective_25c5f20f89f1
-- name    : P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_phiDeriv_injective_25c5f20f89f1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:01.874568+00:00
-- url     : https://prove2.me/theorems/a777d8a2-09d5-4e91-bc38-f7205abf0343
-- title:
--   P2 M Ground Theory Heights  Heights Frame Implicit Graph phi Deriv injective 25c5f20f89f1: P2 M Ground Theory Heights  Heights Frame Implicit Graph phi Deriv injective 25c5f20f89f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Frame Implicit Graph phi Deriv injective 25c5f20f89f1 construction uses the P2 M Ground Theory Heights  Heights Frame Implicit Graph phi Deriv injective 25c5f20f89f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameImplicitGraph.lean#L47-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameImplicitGraph.lean#L47-L84

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

theorem P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_phiDeriv_injective_25c5f20f89f1 (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n))
    (hx : eval (fun i => x i) (frameJacobianDet b I f) ≠ 0) :
    Function.Injective (phiDeriv b I f x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FrameImplicitGraph».«phiDeriv_injective» := P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_phiDeriv_injective_25c5f20f89f1
