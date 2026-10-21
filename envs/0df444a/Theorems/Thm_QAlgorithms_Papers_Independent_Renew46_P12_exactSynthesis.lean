-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P12_exactSynthesis
-- name    : QAlgorithms.Papers.Independent.Renew46.P12.exactSynthesis
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:09:36.40286+00:00
-- url     : https://prove2.me/theorems/d148244c-d3f3-4460-9e53-a3177a2f41c1
-- title:
--   Exact multiqubit Clifford+T synthesis
-- statement:
--   There is an absolute constant $A>0$ such that the following holds for every $n\ge1$ and nonnegative integer $\kappa$. Let $U$ be a unitary on $n$ qubits whose computational-basis entries each admit a representation
--
--   $$
--   U_{ij}=\frac{(a_{ij}+b_{ij}\sqrt2)+i(c_{ij}+d_{ij}\sqrt2)}{(\sqrt2)^\kappa},
--   \qquad a_{ij},b_{ij},c_{ij},d_{ij}\in\mathbb Z.
--   $$
--
--   There are an integer $0\le w\le2$ and a Hadamard, T and CNOT circuit $C$ on $n+w$ wires such that
--
--   $$
--   C\bigl(|\psi\rangle|0^w\rangle\bigr)=(U|\psi\rangle)|0^w\rangle
--   \quad\text{for every }|\psi\rangle,
--   \qquad |C|\le A4^n n(\kappa+1).
--   $$
--
--   The ancillas occupy fixed trailing wires, are returned exactly to zero, and the equality retains global phase. The exponent is a common representation bound, without a minimality condition. This is an exact synthesis guarantee for the indicated arithmetic unitaries.
--
--   **Formalization Note** The displayed bound uses $\kappa+1$ to retain the zero-exponent endpoint. For positive $\kappa$ it is the printed asymptotic bound; at $\kappa=0$, a literal factor $\kappa$ would incorrectly require zero gates even for X.
-- source:
--   Synthesis of unitaries with Clifford+T circuits, arXiv:1306.3200v1, PDF p. 1, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P12

namespace QAlgorithms.Papers.Independent.Renew46.P12

noncomputable section

/-- Theorem 2, PDF p.1, proof p.2: exact, phase-sensitive implementation using at
most two clean ancillas. Endpoint correction: the printed O(4^n n kappa) is written
with kappa+1, because kappa=0 includes X and cannot force a zero-gate circuit; the
proof itself raises the denominator exponent to kappa+1. This retains all zero-exponent
inputs and is the same asymptotic bound for positive exponents. -/
theorem exactSynthesis :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n → ∀ kappa : ℕ,
      ∀ U : Matrix (Qubits n) (Qubits n) ℂ,
        U ∈ Matrix.unitaryGroup (Qubits n) ℂ →
        (∀ i j, HasDenominator (Real.sqrt 2) kappa (U i j)) →
      ∃ w : ℕ, w ≤ 2 ∧ ∃ c : Circuit htcxGateSet (n + w),
        ImplementsWithCleanAncillas c.unitary U ∧
        (c.size : ℝ) ≤ A * (4 : ℝ) ^ n * (n : ℝ) * ((kappa : ℝ) + 1) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P12
