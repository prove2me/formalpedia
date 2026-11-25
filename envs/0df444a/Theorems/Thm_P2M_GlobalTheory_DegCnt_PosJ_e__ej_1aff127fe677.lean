-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DegCnt_PosJ_e__ej_1aff127fe677
-- name    : P2M_GlobalTheory_DegCnt_PosJ_e__ej_1aff127fe677
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:24.8998+00:00
-- url     : https://prove2.me/theorems/c61d7a2f-679f-4ffa-8e8c-d613506c0a30
-- title:
--   P2 M Global Theory Deg Cnt Pos J e  ej 1aff127fe677: P2 M Global Theory Deg Cnt Pos J e  ej 1aff127fe677
-- statement:
--   The P2 M Global Theory Deg Cnt Pos J e  ej 1aff127fe677 construction uses the P2 M Global Theory Deg Cnt Pos J e  ej 1aff127fe677 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L571-L573
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L571-L573

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosJ
open GlobalTheory.HL Matrix Formalism.MainNotions.S.Loc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
variable (N : NF H r)
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem P2M_GlobalTheory_DegCnt_PosJ_e__ej_1aff127fe677 (a : Fin (r + 1)) (ha : N.j ≤ (a : ℕ)) (b : Fin N.j) :
    H.B (N.F'.e a) (ej N.F N.j_le b) = 0 := by sorry

alias «GlobalTheory».«DegCnt».«PosJ».«e'_ej» := P2M_GlobalTheory_DegCnt_PosJ_e__ej_1aff127fe677
