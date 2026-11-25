-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DegCnt_NFGeom_mem_perp__b010c7cdb5ee
-- name    : P2M_GlobalTheory_DegCnt_NFGeom_mem_perp__b010c7cdb5ee
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:26.422096+00:00
-- url     : https://prove2.me/theorems/6701ed49-3237-40c7-be6f-c84aa391d013
-- title:
--   P2 M Global Theory Deg Cnt NFGeom mem perp  b010c7cdb5ee: P2 M Global Theory Deg Cnt NFGeom mem perp  b010c7cdb5ee
-- statement:
--   The P2 M Global Theory Deg Cnt NFGeom mem perp  b010c7cdb5ee construction uses the P2 M Global Theory Deg Cnt NFGeom mem perp  b010c7cdb5ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormGeometrySummary.lean#L477-L480
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormGeometrySummary.lean#L477-L480

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
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r)
omit [NumberField K]

theorem P2M_GlobalTheory_DegCnt_NFGeom_mem_perp__b010c7cdb5ee (S : Submodule K V) (y : V) :
    y ∈ _root_.GlobalTheory.HermLat.perp H S ↔ ∀ x ∈ S, H.B x y = 0 := by sorry

alias «GlobalTheory».«DegCnt».«NFGeom».«mem_perp'» := P2M_GlobalTheory_DegCnt_NFGeom_mem_perp__b010c7cdb5ee
