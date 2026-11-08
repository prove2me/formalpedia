-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_not_baseLevelTwoDecoderSmallError_of_nontrivial_cocycle
-- name    : QEC.Coding.MultiscaleDecoder.not_baseLevelTwoDecoderSmallError_of_nontrivial_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:20:56.880431+00:00
-- url     : https://prove2.me/theorems/1429e321-36cb-4dad-a1a1-5dd4dd08029f
-- title:
--   Multiscale Decoder: not base Level Two Decoder Small Error of nontrivial cocycle
-- statement:
--   Zero-syndrome regression: if level two has a cocycle outside the first
--   coboundaries, the historical syndrome-support-only universal predicate is
--   false for every decoder.  The proof needs no assumption about `decode 0`: the
--   old predicate applied to the zero error first forces `decode 0` to be a
--   coboundary, and applying it to the logical cocycle gives the contradiction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Multiscale.lean#L1330-L1376
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Multiscale.lean#L1330-L1376

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

theorem QEC.Coding.MultiscaleDecoder.not_baseLevelTwoDecoderSmallError_of_nontrivial_cocycle
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth)
    (center : V (levelTwoIndex hdepth))
    (syndromeLocation : C2 (levelTwoIndex hdepth) → V (levelTwoIndex hdepth))
    (decode : BaseLevelTwoDecoder D G hdepth)
    (error : D.family.Correction (levelTwoIndex hdepth))
    (hCocycle : D.family.coboundary1 (levelTwoIndex hdepth) error = 0)
    (hNontrivial : error ∉
      (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier) :
    ¬ BaseLevelTwoDecoderSmallError D G hdepth decode := by sorry
