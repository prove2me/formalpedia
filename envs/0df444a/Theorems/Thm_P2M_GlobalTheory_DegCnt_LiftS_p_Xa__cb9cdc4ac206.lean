-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DegCnt_LiftS_p_Xa__cb9cdc4ac206
-- name    : P2M_GlobalTheory_DegCnt_LiftS_p_Xa__cb9cdc4ac206
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:55:40.717842+00:00
-- url     : https://prove2.me/theorems/823c6330-5da4-414c-b1cb-7cf75c94e102
-- title:
--   P2 M Global Theory Deg Cnt Lift S p Xa  cb9cdc4ac206: P2 M Global Theory Deg Cnt Lift S p Xa  cb9cdc4ac206
-- statement:
--   The P2 M Global Theory Deg Cnt Lift S p Xa  cb9cdc4ac206 construction uses the P2 M Global Theory Deg Cnt Lift S p Xa  cb9cdc4ac206 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean#L337-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean#L337-L338

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

theorem P2M_GlobalTheory_DegCnt_LiftS_p_Xa__cb9cdc4ac206 {y : V} (hy : y ∈ N.F'.Xa N.j) : pI N y = 0 := by sorry

alias «GlobalTheory».«DegCnt».«LiftS».«p_Xa'» := P2M_GlobalTheory_DegCnt_LiftS_p_Xa__cb9cdc4ac206
