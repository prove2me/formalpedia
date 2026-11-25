-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DegCnt_FixDisc_idx_gmap__5fad5dddc642
-- name    : P2M_GlobalTheory_DegCnt_FixDisc_idx_gmap__5fad5dddc642
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:18:34.621568+00:00
-- url     : https://prove2.me/theorems/c7650c46-d68a-47c5-a70d-aadf9b777f49
-- title:
--   P2 M Global Theory Deg Cnt Fix Disc idx gmap  5fad5dddc642: P2 M Global Theory Deg Cnt Fix Disc idx gmap  5fad5dddc642
-- statement:
--   The P2 M Global Theory Deg Cnt Fix Disc idx gmap  5fad5dddc642 construction uses the P2 M Global Theory Deg Cnt Fix Disc idx gmap  5fad5dddc642 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DiscriminantOrderCommonFixedLatticeEmbeddedData.lean#L95-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DiscriminantOrderCommonFixedLatticeEmbeddedData.lean#L95-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DiscriminantOrderCommonFixedLatticeEmbeddedData
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FixDisc
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem P2M_GlobalTheory_DegCnt_FixDisc_idx_gmap__5fad5dddc642 [FiniteDimensional K V] {A B C D : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A)
    (hB : Submodule.IsLattice K B) (hC : Submodule.IsLattice K C) (F : V ≃ₗ[K] V) (hBC : B ≤ C)
    (hDC : D ≤ C) (hi : idxN C B = idxN C D) (hDA : D ≤ A) (h2 : gmap F B ≤ A) :
    (idxN A (gmap F B) : ℚ) = |Algebra.norm ℚ (LinearMap.det (F : V →ₗ[K] V))| * idxN A D := by sorry

alias «GlobalTheory».«DegCnt».«FixDisc».«idx_gmap'» := P2M_GlobalTheory_DegCnt_FixDisc_idx_gmap__5fad5dddc642
