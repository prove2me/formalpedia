-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_topParity_rzMap_map2
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.topParity_rzMap_map2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:26:06.121402+00:00
-- url     : https://prove2.me/theorems/c21a4f4b-2d98-4592-98c2-cc38a6934902
-- title:
--   RZCoarse Graining: top Parity rz Map map2
-- statement:
--   Disjoint supported lifts recover their input by taking each region's parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L152-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L152-L168

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open QEC.Coding.MultiscaleDecoder.RZCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {V : Type v} [Fintype V] [DecidableEq V]
open RZCoarseGrainingData

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.topParity_rzMap_map2
    (A : RZCoarseGrainingData D i V) (w : D.family.Cochain2 i.castSucc) :
    topParity A ((D.rzMap i).map2 w) = w := by sorry
