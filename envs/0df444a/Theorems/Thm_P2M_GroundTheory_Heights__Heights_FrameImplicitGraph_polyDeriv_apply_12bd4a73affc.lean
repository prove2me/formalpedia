-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_polyDeriv_apply_12bd4a73affc
-- name    : P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_polyDeriv_apply_12bd4a73affc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:12.127414+00:00
-- url     : https://prove2.me/theorems/1b167606-57f4-4838-a2ab-9b790c797810
-- title:
--   P2 M Ground Theory Heights  Heights Frame Implicit Graph poly Deriv apply 12bd4a73affc: P2 M Ground Theory Heights  Heights Frame Implicit Graph poly Deriv apply 12bd4a73affc
-- statement:
--   The P2 M Ground Theory Heights  Heights Frame Implicit Graph poly Deriv apply 12bd4a73affc construction uses the P2 M Ground Theory Heights  Heights Frame Implicit Graph poly Deriv apply 12bd4a73affc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameImplicitGraph.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameImplicitGraph.lean#L20-L22

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

theorem P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_polyDeriv_apply_12bd4a73affc (p : MvPolynomial (Fin n) ℂ) (x v : EuclideanSpace ℂ (Fin n)) :
    polyDeriv p x v = ∑ l, eval (fun i => x i) (pderiv l p) * v l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FrameImplicitGraph».«polyDeriv_apply» := P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_polyDeriv_apply_12bd4a73affc
