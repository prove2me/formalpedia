-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DegCnt_NFGeom_z__eq_1a1eccca2614
-- name    : P2M_GlobalTheory_DegCnt_NFGeom_z__eq_1a1eccca2614
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:19.651262+00:00
-- url     : https://prove2.me/theorems/1f07b015-c30d-49c3-9e9b-54a2a2b8a459
-- title:
--   P2 M Global Theory Deg Cnt NFGeom z  eq 1a1eccca2614: P2 M Global Theory Deg Cnt NFGeom z  eq 1a1eccca2614
-- statement:
--   The P2 M Global Theory Deg Cnt NFGeom z  eq 1a1eccca2614 construction uses the P2 M Global Theory Deg Cnt NFGeom z  eq 1a1eccca2614 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormGeometrySummary.lean#L50-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormGeometrySummary.lean#L50-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.NFGeom
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

theorem P2M_GlobalTheory_DegCnt_NFGeom_z__eq_1a1eccca2614 : N.F'.z = N.c • N.F.z := by sorry

alias «GlobalTheory».«DegCnt».«NFGeom».«z'_eq» := P2M_GlobalTheory_DegCnt_NFGeom_z__eq_1a1eccca2614
