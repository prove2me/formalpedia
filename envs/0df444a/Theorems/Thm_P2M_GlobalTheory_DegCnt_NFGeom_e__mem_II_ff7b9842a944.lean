-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DegCnt_NFGeom_e__mem_II_ff7b9842a944
-- name    : P2M_GlobalTheory_DegCnt_NFGeom_e__mem_II_ff7b9842a944
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:16:26.199413+00:00
-- url     : https://prove2.me/theorems/cdf11814-4612-5b0f-be3f-be1105e2a0f9
-- title:
--   P2 M Global Theory Deg Cnt NFGeom e  mem II ff7b9842a944: P2 M Global Theory Deg Cnt NFGeom e  mem II ff7b9842a944
-- statement:
--   The P2 M Global Theory Deg Cnt NFGeom e  mem II ff7b9842a944 construction uses the P2 M Global Theory Deg Cnt NFGeom e  mem II ff7b9842a944 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormGeometrySummary.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormGeometrySummary.lean#L70-L74

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

theorem P2M_GlobalTheory_DegCnt_NFGeom_e__mem_II_ff7b9842a944 (a : Fin r)
    (h : N.j ≤ a.val) :
    N.F'.e a.castSucc ∈ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' := by sorry

alias «GlobalTheory».«DegCnt».«NFGeom».«e'_mem_II» := P2M_GlobalTheory_DegCnt_NFGeom_e__mem_II_ff7b9842a944
