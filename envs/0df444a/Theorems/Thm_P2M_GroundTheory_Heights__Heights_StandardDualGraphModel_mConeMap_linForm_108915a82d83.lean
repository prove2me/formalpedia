-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_mConeMap_linForm_108915a82d83
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_mConeMap_linForm_108915a82d83
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:31.290583+00:00
-- url     : https://prove2.me/theorems/c0299c16-2adc-4cba-89ae-4310879cb4ad
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Graph Model m Cone Map lin Form 108915a82d83: P2 M Ground Theory Heights  Heights Standard Dual Graph Model m Cone Map lin Form 108915a82d83
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Graph Model m Cone Map lin Form 108915a82d83 construction uses the P2 M Ground Theory Heights  Heights Standard Dual Graph Model m Cone Map lin Form 108915a82d83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdGraphModel.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdGraphModel.lean#L18-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdImageBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdGraphModel
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
open GroundTheory.Heights₂.Heights.StandardDualGraphModel
open StandardDualImageBottom
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_mConeMap_linForm_108915a82d83 (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (q : Σ _ : Unit, Fin i) :
    mConeMap (dualLatticeCoord b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b) q) =
      C (aeval (dualLatticeCoord b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b) q)) * X () := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualGraphModel».«mConeMap_linForm» := P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_mConeMap_linForm_108915a82d83
