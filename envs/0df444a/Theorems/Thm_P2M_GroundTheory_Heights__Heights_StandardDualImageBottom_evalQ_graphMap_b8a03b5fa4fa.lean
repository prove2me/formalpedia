-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_evalQ_graphMap_b8a03b5fa4fa
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_evalQ_graphMap_b8a03b5fa4fa
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:38.370456+00:00
-- url     : https://prove2.me/theorems/bb4b0c64-2133-45b4-972c-86fe102202de
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Image Bottom eval Q graph Map b8a03b5fa4fa: P2 M Ground Theory Heights  Heights Standard Dual Image Bottom eval Q graph Map b8a03b5fa4fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Image Bottom eval Q graph Map b8a03b5fa4fa construction uses the P2 M Ground Theory Heights  Heights Standard Dual Image Bottom eval Q graph Map b8a03b5fa4fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdImageBot.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdImageBot.lean#L51-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_SingleMemDualLatticeStandard
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdImageBot
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualImageBottom
open DualArithmeticVariety
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_evalQ_graphMap_b8a03b5fa4fa (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (f : MRing (PBlk i)) :
    evalQ b (graphMap (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))
      (rename (inrV (ι := dualBlocks T) (ι₂ := PBlk i)) f)) = aeval (genPt K i) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualImageBottom».«evalQ_graphMap» := P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_evalQ_graphMap_b8a03b5fa4fa
