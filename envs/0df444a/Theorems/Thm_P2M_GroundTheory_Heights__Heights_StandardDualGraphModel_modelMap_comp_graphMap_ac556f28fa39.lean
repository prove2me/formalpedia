-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_modelMap_comp_graphMap_ac556f28fa39
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_modelMap_comp_graphMap_ac556f28fa39
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:11.391286+00:00
-- url     : https://prove2.me/theorems/57983aab-6842-4982-9527-dbee73fdfa11
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Graph Model model Map comp graph Map ac556f28fa39: P2 M Ground Theory Heights  Heights Standard Dual Graph Model model Map comp graph Map ac556f28fa39
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Graph Model model Map comp graph Map ac556f28fa39 construction uses the P2 M Ground Theory Heights  Heights Standard Dual Graph Model model Map comp graph Map ac556f28fa39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdGraphModel.lean#L51-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdGraphModel.lean#L51-L63

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

theorem P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_modelMap_comp_graphMap_ac556f28fa39 [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    (modelMap b).comp (graphMap (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))) =
      (eval₂Hom (Int.castRingHom (dualStdModelField K i)) (dualStdModelPt b) :
        MRing (Sum.elim (dualBlocks T) (PBlk i)) →+* dualStdModelField K i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualGraphModel».«modelMap_comp_graphMap» := P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_modelMap_comp_graphMap_ac556f28fa39
