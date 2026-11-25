-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DegCnt_LiftS_e__eq_6ca77138a685
-- name    : P2M_GlobalTheory_DegCnt_LiftS_e__eq_6ca77138a685
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:25:57.882232+00:00
-- url     : https://prove2.me/theorems/2e0482b3-cdbb-5a17-b604-58d3a41fea20
-- title:
--   P2 M Global Theory Deg Cnt Lift S e  eq 6ca77138a685: P2 M Global Theory Deg Cnt Lift S e  eq 6ca77138a685
-- statement:
--   The P2 M Global Theory Deg Cnt Lift S e  eq 6ca77138a685 construction uses the P2 M Global Theory Deg Cnt Lift S e  eq 6ca77138a685 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean#L300-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean#L300-L301

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

theorem P2M_GlobalTheory_DegCnt_LiftS_e__eq_6ca77138a685 (b : Fin r) (hb : N.j ≤ b.val) : N.F'.e b.castSucc = N.c • N.F.e b.castSucc := by sorry

alias «GlobalTheory».«DegCnt».«LiftS».«e'_eq» := P2M_GlobalTheory_DegCnt_LiftS_e__eq_6ca77138a685
