-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P39_traceFidelity_frobenius
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P39.traceFidelity_frobenius
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:45:08.884571+00:00
-- url     : https://prove2.me/theorems/bc37abe7-5b3b-4dfe-93cc-5f843bde85cd
-- title:
--   Real trace fidelity and Frobenius distance
-- statement:
--   Let $n\ge0$, $N=2^n$, and let $U,V\in U(N)$ be unitary matrices in the computational basis. Define the phase-sensitive real trace fidelity by $F_{\rm tr}(U,V)=\operatorname{Re}\operatorname{tr}(V^\dagger U)/N$. Then
--
--   $$F_{\rm tr}(U,V)=\frac{\operatorname{Re}\operatorname{tr}(V^\dagger U)}{N}=1-\frac{\|V-U\|_F^2}{2N},\qquad\|V-U\|_F^2=\sum_{a,b}|(V-U)_{ab}|^2.$$
--
--   This identity uses the Frobenius norm and retains global phase. In particular the fidelity can be negative; for $U=-V$ it is $-1$.
-- source:
--   Quantum CISC Compilation by Optimal Control and Scalable Assembly of Complex Instruction Sets beyond Two-Qubit Gates, arXiv:0712.3227v2, PDF p. 5, Real trace fidelity and Frobenius identity, Eq. (14)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P39

namespace QAlgorithms.Papers.Independent.Intakethird100.P39

open scoped BigOperators

/-- PDF p.5, Eq. (14). The distance is explicitly the squared Frobenius
norm; arbitrary real trace fidelity, including -1, is allowed. -/
theorem traceFidelity_frobenius (n : ℕ)
    (U V : Matrix (Qubits n) (Qubits n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    traceFidelity U V = (Matrix.trace (star V * U)).re / (2 : ℝ) ^ n ∧
    traceFidelity U V = 1 -
      (∑ a : Qubits n, ∑ b : Qubits n, Complex.normSq ((V - U) a b)) /
        (2 * (2 : ℝ) ^ n) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P39
