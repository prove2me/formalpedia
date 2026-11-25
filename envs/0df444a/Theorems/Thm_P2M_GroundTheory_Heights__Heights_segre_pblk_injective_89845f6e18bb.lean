-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_pblk_injective_89845f6e18bb
-- name    : P2M_GroundTheory_Heights__Heights_segre_pblk_injective_89845f6e18bb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:51:06.189297+00:00
-- url     : https://prove2.me/theorems/bb26983a-e4d8-4747-a297-9d3f0e321388
-- title:
--   P2 M Ground Theory Heights  Heights segre pblk injective 89845f6e18bb: P2 M Ground Theory Heights  Heights segre pblk injective 89845f6e18bb
-- statement:
--   The P2 M Ground Theory Heights  Heights segre pblk injective 89845f6e18bb construction uses the P2 M Ground Theory Heights  Heights segre pblk injective 89845f6e18bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetParam.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetParam.lean#L24-L29

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

theorem P2M_GroundTheory_Heights__Heights_segre_pblk_injective_89845f6e18bb : Function.Injective (segre : ((Σ k, PBlk n k) → ℂ) → _) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«segre_pblk_injective» := P2M_GroundTheory_Heights__Heights_segre_pblk_injective_89845f6e18bb
