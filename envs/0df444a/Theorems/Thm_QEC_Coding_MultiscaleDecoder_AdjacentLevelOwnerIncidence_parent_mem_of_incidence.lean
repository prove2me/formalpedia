-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_AdjacentLevelOwnerIncidence_parent_mem_of_incidence
-- name    : QEC.Coding.MultiscaleDecoder.AdjacentLevelOwnerIncidence.parent_mem_of_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:21:12.796912+00:00
-- url     : https://prove2.me/theorems/1023c3fe-21de-49b9-b3bd-9fc5d9bfb43d
-- title:
--   Adjacent Level Owner Incidence: parent mem of incidence
-- statement:
--   The Adjacent Level Owner Incidence construction uses the parent mem of incidence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Multiscale.lean#L981-L986
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Multiscale.lean#L981-L986

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

theorem QEC.Coding.MultiscaleDecoder.AdjacentLevelOwnerIncidence.parent_mem_of_incidence
    (A : AdjacentLevelOwnerIncidence depth V SyndromeCoord CorrectionCoord G)
    (i : StepIndex depth) (u : V i.castSucc) (v : V i.succ)
    (h : A.parentIncidence i v = some u) :
    G.interLevel i u v = true := by sorry
