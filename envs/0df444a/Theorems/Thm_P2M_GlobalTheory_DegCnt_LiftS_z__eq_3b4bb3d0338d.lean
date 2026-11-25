-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DegCnt_LiftS_z__eq_3b4bb3d0338d
-- name    : P2M_GlobalTheory_DegCnt_LiftS_z__eq_3b4bb3d0338d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:42:18.22996+00:00
-- url     : https://prove2.me/theorems/87c344fd-0eb8-4b5c-b29c-f6ad91db4433
-- title:
--   P2 M Global Theory Deg Cnt Lift S z  eq 3b4bb3d0338d: P2 M Global Theory Deg Cnt Lift S z  eq 3b4bb3d0338d
-- statement:
--   The P2 M Global Theory Deg Cnt Lift S z  eq 3b4bb3d0338d construction uses the P2 M Global Theory Deg Cnt Lift S z  eq 3b4bb3d0338d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean#L303-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean#L303-L305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_P2M_GlobalTheory_DegCnt_NFGeom_z__eq_1a1eccca2614

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.LiftS
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

theorem P2M_GlobalTheory_DegCnt_LiftS_z__eq_3b4bb3d0338d : N.F'.z = N.c • N.F.z := by sorry

alias «GlobalTheory».«DegCnt».«LiftS».«z'_eq» := P2M_GlobalTheory_DegCnt_LiftS_z__eq_3b4bb3d0338d
