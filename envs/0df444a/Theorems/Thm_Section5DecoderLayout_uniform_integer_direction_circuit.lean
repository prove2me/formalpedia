-- Prove2me | Theorems.Thm_Section5DecoderLayout_uniform_integer_direction_circuit
-- name    : Section5DecoderLayout.uniform_integer_direction_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:58:20.574592+00:00
-- url     : https://prove2.me/theorems/1e2be805-84b8-4ec3-913a-4dd7d2d507d4
-- title:
--   Uniform conditional integer-matrix direction circuit
-- statement:
--   Let n=N+1 and 0<ε<1; choose iteration count K, fractional bits f and integer width b from the source's explicit decoder parameters. There is a reversible circuit on the canonical layout with $$|C|\le10^{36}(n/\varepsilon)^{15}.$$ For clean auxiliary wires and zero later matrix stages, if stage 0 contains integer M with L=2^(−f)op(M) self-adjoint and ‖L−ww*‖≤ε/2000 for real unit w, its decoded output v satisfies v≠0 and min_{s=±1}‖v/‖v‖−sw‖≤ε/6. The theorem assumes the acquired matrix guarantee.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5UniformIntegerDirectionCircuit.lean, lines 13–19. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5DecoderLayout
import Definitions.Def_Section5Verified_Section5DyadicDecoderParameters
import Definitions.Def_Section5Verified_Section5IntegerDirectionCircuit
import Definitions.Def_Section5Verified_Section5IntegerDirectionSpec
import Definitions.Def_Section5Verified_Section5ReconstructionPrecision
import Mathlib
import Theorems.Thm_Section5DecoderLayout_integer_matrix_direction_spec
import Theorems.Thm_Section5DecoderLayout_uniform_decoder_gate_bound
import Theorems.Thm_section5_decoder_parameters_sufficient
import Theorems.Thm_section5_decoder_power_gate_bound
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout

theorem Section5DecoderLayout.uniform_integer_direction_circuit (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    let K := section5_decoder_iterations (N+1) ε
    let f := section5_decoder_fraction_bits (N+1) ε
    let b := section5_decoder_integer_width (N+1) ε
    ∃ circ : Circuit gatesRev (Section5DecoderLayout.width N K b f),
      (circ.size:ℝ) ≤ (10:ℝ)^36*(((N+1:ℕ):ℝ)/ε)^15 ∧
      Section5DecoderLayout.DirectionSpec N K b f f ε circ := by sorry
