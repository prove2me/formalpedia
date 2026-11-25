-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointArithIntersection_logNorm_smul_6dcf290a87aa
-- name    : P2M_GroundTheory_Heights__Heights_PointArithIntersection_logNorm_smul_6dcf290a87aa
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:02.5428+00:00
-- url     : https://prove2.me/theorems/b247269f-7562-41cd-b89b-8365e68f933f
-- title:
--   P2 M Ground Theory Heights  Heights Point Arith Intersection log Norm smul 6dcf290a87aa: P2 M Ground Theory Heights  Heights Point Arith Intersection log Norm smul 6dcf290a87aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Arith Intersection log Norm smul 6dcf290a87aa construction uses the P2 M Ground Theory Heights  Heights Point Arith Intersection log Norm smul 6dcf290a87aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPointArInt.lean#L20-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPointArInt.lean#L20-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPointArInt
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
open GroundTheory.Heights₂.Heights.PointArithIntersection
open IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
variable {T : Type} [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_PointArithIntersection_logNorm_smul_6dcf290a87aa {A : HermLine (fun _ : Unit => T)} {s : MRing (fun _ : Unit => T)}
    {P : Ideal (MRing (fun _ : Unit => T))} (hs : IsSectionOn P A s) (c : ℂ) (hc : c ≠ 0)
    (z : (Σ _ : Unit, T) → ℂ) : logNorm A s (fun p => c * z p) = logNorm A s z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointArithIntersection».«logNorm_smul» := P2M_GroundTheory_Heights__Heights_PointArithIntersection_logNorm_smul_6dcf290a87aa
