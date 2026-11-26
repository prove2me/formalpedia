-- Prove2me | Theorems.Thm_Section5DecoderLayout_integer_matrix_direction_circuit
-- name    : Section5DecoderLayout.integer_matrix_direction_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:45:55.808948+00:00
-- url     : https://prove2.me/theorems/6e0e0273-27b5-5c97-85b8-1138e85e5fe7
-- title:
--   Conditional direction circuit for an acquired integer matrix
-- statement:
--   Let n=N+1≤2^c, (K+1)(q+c+2)<b, f≤(q+1)(K+1) and (q+1)(K+1)+2≤b+1. On the canonical layout, a reversible circuit satisfies $$|C|\le88n^3(b+1)^3K+\operatorname{decoderGateBound}(N,b,f).$$ Start with clean auxiliary wires, zero later matrix stages and integer M in stage 0. If L=2^(−q)op(M) is self-adjoint, 0<ε<1, 2^(K+1)≥800n/ε, 2^f≥144n²4^(K+1)/ε, and real unit w satisfies ‖L−ww*‖≤ε/2000, the decoded output v is nonzero and min_{s=±1}‖v/‖v‖−sw‖≤ε/6.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5IntegerDirectionCircuit.lean, lines 40–58. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Mathlib
import Theorems.Thm_Section5DecoderLayout_canonical_powered_decoder
import Theorems.Thm_section5_dyadic_entry_bound
import Theorems.Thm_section5_exact_integer_matrix_power_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout

theorem Section5DecoderLayout.integer_matrix_direction_circuit (N K b f q c : ℕ)
    (hn : N+1 ≤ 2^c) (hwidth : (K+1)*(q+1+c+1) < b)
    (hf : f ≤ (q+1)*(K+1)) (hfit : (q+1)*(K+1)+2 ≤ b+1) :
    ∃ circ : Circuit gatesRev (Section5DecoderLayout.width N K b f),
      circ.size ≤ (88*(N+1)^3*(b+1)^3)*K+Section5DecoderLayout.decoderGateBound N b f ∧
      ∀ z : Qubits (Section5DecoderLayout.width N K b f), Section5DecoderLayout.Clean z →
        (∀ s : Fin (K+1), 0 < s.val → ∀ i e, z (Section5DecoderLayout.matrix s i e)=false) →
        let M := section5_signed_matrix_read (Section5DecoderLayout.matrix (f:=f) 0) z
        IsSelfAdjoint (M.dyadicOperator q) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        800*((N+1:ℕ):ℝ)/ε ≤ (2:ℝ)^(K+1) →
        144*((N+1:ℕ):ℝ)^2*(4:ℝ)^(K+1)/ε ≤ (2:ℝ)^f →
      ∀ w : EuclideanSpace ℝ (Fin (N+1)), ‖w‖=1 →
        ‖M.dyadicOperator q-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/2000 →
        ∃ z' : Qubits (Section5DecoderLayout.width N K b f), act circ.unitary (ket z)=ket z' ∧
          let v : EuclideanSpace ℝ (Fin (N+1)) := WithLp.toLp 2 fun i => readFp
            (⟨fun e => Section5DecoderLayout.output N K b f i e.rev,
              fun _ _ h => Fin.rev_injective ((Section5DecoderLayout.output N K b f i).injective h)⟩) f z'
          v ≠ 0 ∧ (‖NormedSpace.normalize v-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize v+w‖ ≤ ε/6) := by sorry
