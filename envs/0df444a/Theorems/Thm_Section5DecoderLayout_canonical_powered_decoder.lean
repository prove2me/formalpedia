-- Prove2me | Theorems.Thm_Section5DecoderLayout_canonical_powered_decoder
-- name    : Section5DecoderLayout.canonical_powered_decoder
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:39:59.047957+00:00
-- url     : https://prove2.me/theorems/c5ec9257-661f-5b89-8db3-732e47d81166
-- title:
--   Canonical conditional decoder for an existing matrix power
-- statement:
--   Let n=N+1 and f≤(q+1)(K+1), (q+1)(K+1)+2≤b+1. On the canonical width(N,K,b,f) layout there exists a reversible circuit with the explicit decoder gate bound in the source. For a clean layout whose last stage already contains M^(K+1), assume L=2^(−q)op(M) self-adjoint, 0<ε<1, 2^(K+1)≥800n/ε and 2^f≥144n²4^(K+1)/ε. Whenever real unit w satisfies ‖L−ww*‖≤ε/2000, its public decoded output v obeys $$v\ne0,\qquad\min_{s\in\{\pm1\}}\|v/\|v\|-sw\|\le\varepsilon/6.$$ This is conditional on the supplied powered matrix and proximity estimate.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5CanonicalPoweredDecoder.lean, lines 35–55. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5DecoderLayoutLaws
import Definitions.Def_Section5Verified_Section5ExactMatrixPowerCircuit
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5PoweredMatrixDecoder
import Definitions.Def_Section5Verified_Section5ScoredColumnMatrix
import Mathlib
import Theorems.Thm_Section5DecoderLayout_record_matrix_read
import Theorems.Thm_Section5DecoderLayout_records_columnLabel
import Theorems.Thm_Section5DecoderLayout_records_disjoint
import Theorems.Thm_section5_powered_matrix_decoder_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout

theorem Section5DecoderLayout.canonical_powered_decoder (N K b f q : ℕ)
    (hf : f ≤ (q+1)*(K+1)) (hfit : (q+1)*(K+1)+2 ≤ b+1) :
    ∃ c : Circuit gatesRev (Section5DecoderLayout.width N K b f),
      c.size ≤
        (((16*(2*(N+1)+b+b+1)+6)*(((N+1)+(N+1))*(b+1)*(b+1)))*(N+1)+
          (16*(2*(N+1)+b+b+1)+1+7*(Section5DecoderLayout.recordWidth N b))*N)+
        ((16*((N+1)+b+b+1+1)+6)*(((N+1)+(N+1))*(b+1)*(b+1))+
          7*((N+1)*(b+1))+2*(f+2)*(N+1)) ∧
      ∀ z : Qubits (Section5DecoderLayout.width N K b f), Section5DecoderLayout.Clean z →
      ∀ M : Section5IntegerMatrix (N+1), IsSelfAdjoint (M.dyadicOperator q) →
        section5_signed_matrix_read (Section5DecoderLayout.matrix (f:=f) (Fin.last K)) z=M.power (K+1) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        800*((N+1:ℕ):ℝ)/ε ≤ (2:ℝ)^(K+1) →
        144*((N+1:ℕ):ℝ)^2*(4:ℝ)^(K+1)/ε ≤ (2:ℝ)^f →
      ∀ w : EuclideanSpace ℝ (Fin (N+1)), ‖w‖=1 →
        ‖M.dyadicOperator q-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/2000 →
        ∃ z' : Qubits (Section5DecoderLayout.width N K b f), act c.unitary (ket z)=ket z' ∧
          let v : EuclideanSpace ℝ (Fin (N+1)) := WithLp.toLp 2 fun i => readFp
            (⟨fun e => Section5DecoderLayout.output N K b f i e.rev,
              fun _ _ h => Fin.rev_injective ((Section5DecoderLayout.output N K b f i).injective h)⟩) f z'
          v ≠ 0 ∧ (‖NormedSpace.normalize v-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize v+w‖ ≤ ε/6) := by sorry
