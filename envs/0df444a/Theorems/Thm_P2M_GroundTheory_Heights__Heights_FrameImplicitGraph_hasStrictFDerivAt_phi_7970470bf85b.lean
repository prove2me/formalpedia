-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_hasStrictFDerivAt_phi_7970470bf85b
-- name    : P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_hasStrictFDerivAt_phi_7970470bf85b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:59.116498+00:00
-- url     : https://prove2.me/theorems/b65a664a-0175-4ce0-830f-0cc159ebc89d
-- title:
--   P2 M Ground Theory Heights  Heights Frame Implicit Graph has Strict FDeriv At phi 7970470bf85b: P2 M Ground Theory Heights  Heights Frame Implicit Graph has Strict FDeriv At phi 7970470bf85b
-- statement:
--   The P2 M Ground Theory Heights  Heights Frame Implicit Graph has Strict FDeriv At phi 7970470bf85b construction uses the P2 M Ground Theory Heights  Heights Frame Implicit Graph has Strict FDeriv At phi 7970470bf85b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameImplicitGraph.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameImplicitGraph.lean#L42-L45

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

theorem P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_hasStrictFDerivAt_phi_7970470bf85b (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    HasStrictFDerivAt (phi b I f) (phiDeriv b I f x) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FrameImplicitGraph».«hasStrictFDerivAt_phi» := P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_hasStrictFDerivAt_phi_7970470bf85b
