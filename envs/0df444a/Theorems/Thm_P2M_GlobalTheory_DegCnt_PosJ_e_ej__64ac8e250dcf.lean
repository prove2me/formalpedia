-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DegCnt_PosJ_e_ej__64ac8e250dcf
-- name    : P2M_GlobalTheory_DegCnt_PosJ_e_ej__64ac8e250dcf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:53:45.281225+00:00
-- url     : https://prove2.me/theorems/149927be-7799-4c8a-bac9-fe45c6cbd0e3
-- title:
--   P2 M Global Theory Deg Cnt Pos J e ej  64ac8e250dcf: P2 M Global Theory Deg Cnt Pos J e ej  64ac8e250dcf
-- statement:
--   The P2 M Global Theory Deg Cnt Pos J e ej  64ac8e250dcf construction uses the P2 M Global Theory Deg Cnt Pos J e ej  64ac8e250dcf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L563-L568
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L563-L568

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

theorem P2M_GlobalTheory_DegCnt_PosJ_e_ej__64ac8e250dcf (a : Fin (r + 1)) (ha : N.j ≤ (a : ℕ)) (b : Fin N.j) :
    H.B (N.F.e a) (ej N.F' N.j_le b) = 0 := by sorry

alias «GlobalTheory».«DegCnt».«PosJ».«e_ej'» := P2M_GlobalTheory_DegCnt_PosJ_e_ej__64ac8e250dcf
