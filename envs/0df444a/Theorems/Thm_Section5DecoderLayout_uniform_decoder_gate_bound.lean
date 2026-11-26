-- Prove2me | Theorems.Thm_Section5DecoderLayout_uniform_decoder_gate_bound
-- name    : Section5DecoderLayout.uniform_decoder_gate_bound
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:54.522594+00:00
-- url     : https://prove2.me/theorems/6d31fa57-3a36-42c9-8504-69ccf745a267
-- title:
--   Uniform polynomial bound on canonical decoding gates
-- statement:
--   Let N be natural and 0<ε<1. Let b and f be the explicit integer width and fractional precision of the decoder for n=N+1. The canonical decoding gate bound satisfies $$\operatorname{decoderGateBound}(N,b,f)\le10^{35}((N+1)/\varepsilon)^{15}.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5DecoderGateBound.lean, lines 58–60.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5DyadicDecoderParameters
import Definitions.Def_Section5Verified_Section5IntegerDirectionCircuit
import Mathlib
import Theorems.Thm_Section5DecoderLayout_decoder_gate_bound_polynomial
import Theorems.Thm_section5_decoder_parameters_polynomial
set_option autoImplicit false
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout

theorem Section5DecoderLayout.uniform_decoder_gate_bound (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    (Section5DecoderLayout.decoderGateBound N (section5_decoder_integer_width (N+1) ε)
      (section5_decoder_fraction_bits (N+1) ε):ℝ) ≤ (10:ℝ)^35*(((N+1:ℕ):ℝ)/ε)^15 := by sorry
