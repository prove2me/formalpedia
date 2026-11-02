-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_postselectionState
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.postselectionState
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:35:45.193419+00:00
-- url     : https://prove2.me/theorems/92326181-db31-46e1-980a-dd8112eaf229
-- title:
--   II: effective state and conditional measurement distribution, (1)–(2)
-- statement:
--   Let $n\ge1$, $0\le Q\le\tfrac12$, and let $C=(C_k)_{k\in K}$ be a nonempty family of distinct binary words of length $n$, where $m=|K|$. Write $\rho_Q=(1-2Q)|\Phi^+\rangle\langle\Phi^+|+(Q/2)I_4$, with $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$. Regroup its independent copies as $A^nB^n$. Define $K_C=\sum_k|k\rangle\langle C_k|$ and $P_C=(I\otimes K_C)\rho_Q^{\otimes n}(I\otimes K_C)^\dagger$. The input has trace one and is positive, and $P_C$ is positive. If $p_Q(a,b)$ is the diagonal measurement law of the input, then
--
--   $$\operatorname{Tr}P_C=\Pr(B^n\in C)=\frac{m}{2^n}>0,\qquad
--   \frac{\langle a,k|P_C|a,k\rangle}{\operatorname{Tr}P_C}
--   =\frac{p_Q(a,C_k)}{\Pr(B^n\in C)}.$$
--
--   Thus filtering preserves the complete conditional joint distribution, including Bob's codeword label. The filtered operator itself is unnormalized.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 3, II: effective state and conditional measurement distribution, (1)–(2)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF pp.2–3, (1)–(2): actual filtering, positive acceptance mass m/2^n,
and the complete conditional joint law, rather than only a yes/no event. -/
theorem postselectionState {n : ℕ} (hn : 1 ≤ n) [Nonempty K]
    (C : K → Qubits n) (hC : Function.Injective C) (Q : ℝ)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1 / 2) :
    IsDensityMatrix (sixStateCopies (Fin n) Q) ∧ (bobState C Q).PosSemidef ∧
    (bobState C Q).trace = ((Fintype.card K : ℂ) / 2 ^ n) ∧
    acceptanceMass C Q = (Fintype.card K : ℝ) / 2 ^ n ∧
    0 < acceptanceMass C Q ∧
    ∀ (a : Qubits n) (k : K),
      diagonalLaw (bobState C Q) a k =
        (sixStateCopies (Fin n) Q (a, C k) (a, C k)).re / acceptanceMass C Q := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
