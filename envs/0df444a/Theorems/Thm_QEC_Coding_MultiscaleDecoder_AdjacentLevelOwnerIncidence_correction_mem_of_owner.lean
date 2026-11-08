-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_AdjacentLevelOwnerIncidence_correction_mem_of_owner
-- name    : QEC.Coding.MultiscaleDecoder.AdjacentLevelOwnerIncidence.correction_mem_of_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:21:11.063698+00:00
-- url     : https://prove2.me/theorems/bbc72892-cfda-4a23-bf58-775b66b9ebf6
-- title:
--   Adjacent Level Owner Incidence: correction mem of owner
-- statement:
--   The Adjacent Level Owner Incidence construction uses the correction mem of owner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Multiscale.lean#L974-L979
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Multiscale.lean#L974-L979

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Locality_Graph_Core
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z a
variable {depth : Nat}
open BDL26CochainFamily
open QEC.Coding.MultiscaleDecoder.AdjacentLevelOwnerIncidence
variable {depth : Nat}
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {SyndromeCoord : LevelIndex depth → Type w}
variable [∀ i, Fintype (SyndromeCoord i)]
  [∀ i, DecidableEq (SyndromeCoord i)]
variable {CorrectionCoord : LevelIndex depth → Type x}
variable [∀ i, Fintype (CorrectionCoord i)]
  [∀ i, DecidableEq (CorrectionCoord i)]
variable {G : DecodingGraphFamily depth V}

theorem QEC.Coding.MultiscaleDecoder.AdjacentLevelOwnerIncidence.correction_mem_of_owner
    (A : AdjacentLevelOwnerIncidence depth V SyndromeCoord CorrectionCoord G)
    (i : LevelIndex depth) (c : CorrectionCoord i) (v : V i)
    (h : A.correctionOwner i c = some v) :
    c ∈ A.correctionRegion i v := by sorry
