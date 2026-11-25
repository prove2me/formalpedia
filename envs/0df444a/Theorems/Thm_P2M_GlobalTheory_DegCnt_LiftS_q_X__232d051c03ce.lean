-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DegCnt_LiftS_q_X__232d051c03ce
-- name    : P2M_GlobalTheory_DegCnt_LiftS_q_X__232d051c03ce
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:21:56.652639+00:00
-- url     : https://prove2.me/theorems/cb7f1fcf-d588-4b02-8be5-79b8bd20a437
-- title:
--   P2 M Global Theory Deg Cnt Lift S q X  232d051c03ce: P2 M Global Theory Deg Cnt Lift S q X  232d051c03ce
-- statement:
--   The P2 M Global Theory Deg Cnt Lift S q X  232d051c03ce construction uses the P2 M Global Theory Deg Cnt Lift S q X  232d051c03ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean#L307-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean#L307-L319

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
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

theorem P2M_GlobalTheory_DegCnt_LiftS_q_X__232d051c03ce {y : V} (hy : y ∈ N.F'.X) : qI N y = 0 := by sorry

alias «GlobalTheory».«DegCnt».«LiftS».«q_X'» := P2M_GlobalTheory_DegCnt_LiftS_q_X__232d051c03ce
