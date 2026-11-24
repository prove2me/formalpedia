-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_probMixed_pad_stability
-- name    : QuantumLTF.Membership.Supplement.probMixed_pad_stability
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-24T19:23:52.893173+00:00
-- url     : https://prove2.me/theorems/97cc08da-cb9a-4410-868c-bec070fc43e7
-- title:
--   Tomography measurement stability under input trace-distance error
-- statement:
--   Let two Hermitian input operators have equal trace. Append the same clean ancillas to each, apply the same unitary, and measure any event in the computational basis. The difference in event probabilities is bounded by half the trace norm of the original input difference:
--   $$|p_\rho(P)-p_\sigma(P)|\leq\tfrac12\|\rho-\sigma\|_1.$$
--   For density operators this is the usual trace-distance stability guarantee. It supplies the robustness transfer in Section 5.4 and Theorem 5.6: any success bound on ideal tensor-power input loses at most the input trace distance on the actual noisy state. The unitary may include a coherent reversible implementation of the final classical post-processing.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Section 5.4, Theorem 5.6, Eq. (189). Generalized to all equal-trace Hermitian operators. Uses the proved positive trace-preserving contraction theorem of Perez-Garcia, Wolf, Petz, Ruskai, arXiv:math-ph/0601063.

import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QuantumLTF_Membership_Supplement_padDensity
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
open QAlgorithms

theorem QuantumLTF.Membership.Supplement.probMixed_pad_stability {N a : ℕ}
    (U : Matrix (Qubits (N+a)) (Qubits (N+a)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits (N+a)) ℂ)
    (ρ σ : Matrix (Qubits N) (Qubits N) ℂ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (ht : ρ.trace = σ.trace)
    (P : Qubits (N+a) → Prop) [DecidablePred P] :
    |QuantumLTF.Membership.Supplement.probMixed U
        (QuantumLTF.Membership.Supplement.padDensity a ρ) P -
      QuantumLTF.Membership.Supplement.probMixed U
        (QuantumLTF.Membership.Supplement.padDensity a σ) P| ≤ traceNorm (ρ-σ) / 2 := by sorry
