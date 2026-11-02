-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_binary_reencoding
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.binary_reencoding
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:59:01.416369+00:00
-- url     : https://prove2.me/theorems/1be06a6e-aed3-430b-959d-0e7fb884e4f4
-- title:
--   Appendix D: binary encoding uses exponentially fewer address qubits
-- statement:
--   Fix a normalized pure sample family, anchor, history of length $T$, and $q$ with $2^q\ge T+1$. Initialize the binary address at zero. The Appendix-D product of coherent anchor tests with cyclic increments and address-selective reflections is exactly the unary erasure state with each unary $|t\rangle$ replaced by binary $|t\rangle$:
--
--   $$V_{\rm binary}(|\psi\rangle|0\rangle)=\operatorname{Encode}_{q,T}\!\left[|\phi_a\rangle\sum_{t<T}\langle\phi_a|\psi_t\rangle|t\rangle+|\psi_T\rangle|T\rangle\right],\qquad\lceil\log_2(T+1)\rceil\le q.$$
--
--   The ideal main-system output is therefore unchanged. There are absolute constants and a sample-only circuit family, fixed before unknown samples, $U$ and the new input, using $(4T+1)m+1$ supplied copies and at most $C(4T+1)mn(q+1)$ elementary gates on $n$-qubit systems. Its averaged distance from the same ideal emulator is at most $c(4T+1)/m$. Apart from supplied-copy registers and the main register, at most $q+3$ helper/address/measurement wires suffice. Thus the reflection sample/error bounds are preserved while the gate overhead is $O(q+1)$. The constant helper wires are excluded from the advertised address count.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 22, Appendix D: binary encoding uses exponentially fewer address qubits

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF pp.22–23, Appendix D: exact binary/unary erasure equality, same ideal
main output, and source sample/gate costs for its sample-copy implementation. The q address
qubits exclude the constant helper/measurement qubits. D8's initial |t> is replaced by |0>;
D9's tensor grouping and |0> helper are corrected to Fig.6's returned |minus>.
Using q+1 (equivalently log(T+1) away from T=0) handles the small-T boundary. -/
theorem binary_reencoding :
    (∀ (phi : K → EuclideanSpace ℂ I) (a : K), (∀ k, IsState (phi k)) →
      ∀ (q T : ℕ), T+1 ≤ 2^q → ∀ (h : Fin T → K) (psi : EuclideanSpace ℂ I), IsState psi →
        act (binaryHistory phi a q h) (tensorVec psi (ket (0 : Fin (2^q)))) =
          encodeUnary q T (coordinateExpansion phi a h psi) ∧
        Nat.clog 2 (T+1) ≤ q) ∧
    (∃ (C c : ℝ) (B : BinaryEmulatorFamily), 0 < C ∧ 0 < c ∧
      ∀ (n k : ℕ), 2 ≤ k → ∀ (a : Fin k) (q T m : ℕ),
        T+1 ≤ 2^q → 1 ≤ m →
        (∀ h : Fin T → Fin k,
          (B n k a q T m h).copies = (4*T+1)*m+1 ∧
          (B n k a q T m h).N ≤ ((4*T+1)*m+2)*n + q+3 ∧
          ((B n k a q T m h).gates.length : ℝ) ≤ C * (4*T+1) * m * n * (q+1)) ∧
        ∀ (phi : Fin k → EuclideanSpace ℂ (Qubits n)), (∀ j, IsState (phi j)) →
          ∀ (U : Matrix.unitaryGroup (Qubits n) ℂ) (rho : Matrix (Qubits n) (Qubits n) ℂ), IsDensityMatrix rho →
          traceDistance
            (∑ h : Fin T → Fin k, (historyWeight (nonanchorProbability a) h : ℂ) •
              (B n k a q T m h).output (inputOutputRecords phi (U : Matrix (Qubits n) (Qubits n) ℂ)) rho)
            (emulate phi a (U : Matrix (Qubits n) (Qubits n) ℂ) T rho) ≤ c * (4*T+1) / m) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
