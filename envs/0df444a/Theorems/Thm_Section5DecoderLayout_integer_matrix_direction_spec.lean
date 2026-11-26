-- Prove2me | Theorems.Thm_Section5DecoderLayout_integer_matrix_direction_spec
-- name    : Section5DecoderLayout.integer_matrix_direction_spec
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:52:28.170134+00:00
-- url     : https://prove2.me/theorems/51ee7dc4-6a4d-5fb5-bb59-35f275d92166
-- title:
--   Explicit basis-state specification for integer direction recovery
-- statement:
--   Let n=N+1≤2^c, (K+1)(q+c+2)<b, f≤(q+1)(K+1), (q+1)(K+1)+2≤b+1, 0<ε<1, 2^(K+1)≥800n/ε and 2^f≥144n²4^(K+1)/ε. There exists a reversible circuit satisfying $$|C|\le88n^3(b+1)^3K+\operatorname{decoderGateBound}(N,b,f).$$ Its basis-state specification is: on clean auxiliary registers, zero later matrix stages and an initial integer matrix M whose L=2^(−q)op(M) is self-adjoint and within ε/2000 of ww* for real unit w, the output v is nonzero and min_{s=±1}‖v/‖v‖−sw‖≤ε/6.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5IntegerDirectionSpec.lean, lines 25–32.

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
import Definitions.Def_Section5Verified_Section5CanonicalPoweredDecoder
import Definitions.Def_Section5Verified_Section5DecoderLayout
import Definitions.Def_Section5Verified_Section5ExactMatrixPowerCircuit
import Definitions.Def_Section5Verified_Section5IntegerDirectionCircuit
import Definitions.Def_Section5Verified_Section5IntegerDirectionSpec
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Mathlib
import Theorems.Thm_Section5DecoderLayout_integer_matrix_direction_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout

theorem Section5DecoderLayout.integer_matrix_direction_spec (N K b f q c : ℕ)
    (hn : N+1 ≤ 2^c) (hwidth : (K+1)*(q+1+c+1) < b)
    (hf : f ≤ (q+1)*(K+1)) (hfit : (q+1)*(K+1)+2 ≤ b+1)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hiter : 800*((N+1:ℕ):ℝ)/ε ≤ (2:ℝ)^(K+1))
    (hbits : 144*((N+1:ℕ):ℝ)^2*(4:ℝ)^(K+1)/ε ≤ (2:ℝ)^f) :
    ∃ circ : Circuit gatesRev (Section5DecoderLayout.width N K b f),
      circ.size ≤ (88*(N+1)^3*(b+1)^3)*K+Section5DecoderLayout.decoderGateBound N b f ∧ Section5DecoderLayout.DirectionSpec N K b f q ε circ := by sorry
