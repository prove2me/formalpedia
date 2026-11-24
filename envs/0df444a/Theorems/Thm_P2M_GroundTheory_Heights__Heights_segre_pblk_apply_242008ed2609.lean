-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_pblk_apply_242008ed2609
-- name    : P2M_GroundTheory_Heights__Heights_segre_pblk_apply_242008ed2609
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:15.52116+00:00
-- url     : https://prove2.me/theorems/3d4449b0-5165-4138-91d7-cc211b50b733
-- title:
--   P2 M Ground Theory Heights  Heights segre pblk apply 242008ed2609: P2 M Ground Theory Heights  Heights segre pblk apply 242008ed2609
-- statement:
--   The P2 M Ground Theory Heights  Heights segre pblk apply 242008ed2609 construction uses the P2 M Ground Theory Heights  Heights segre pblk apply 242008ed2609 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetParam.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetParam.lean#L20-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre mcPts
  IsMultiHomogIdeal mcPts_smul)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_segre_pblk_apply_242008ed2609 (z : (Σ k, PBlk n k) → ℂ) (i : (k : Unit) → PBlk n k) :
    segre z i = z ⟨(), i ()⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«segre_pblk_apply» := P2M_GroundTheory_Heights__Heights_segre_pblk_apply_242008ed2609
