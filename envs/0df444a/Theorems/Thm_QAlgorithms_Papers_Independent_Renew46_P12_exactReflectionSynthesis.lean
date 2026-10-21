-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P12_exactReflectionSynthesis
-- name    : QAlgorithms.Papers.Independent.Renew46.P12.exactReflectionSynthesis
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:11:09.185605+00:00
-- url     : https://prove2.me/theorems/fab77c35-0cd2-4444-a614-5c7ae80c7a48
-- title:
--   Exact synthesis of arithmetic reflections
-- statement:
--   There is an absolute constant $A>0$ such that, for every $n\ge1$ and nonnegative integer $\kappa$, every normalized $n$-qubit vector $|\phi\rangle$ with coordinates
--
--   $$
--   \phi_j=\frac{(a_j+b_j\sqrt2)+i(c_j+d_j\sqrt2)}{(\sqrt2)^\kappa},
--   \qquad a_j,b_j,c_j,d_j\in\mathbb Z,
--   $$
--
--   has a reflection $R_\phi=I-2|\phi\rangle\langle\phi|$ exactly implemented by a Hadamard, T and CNOT circuit C with $w\le1$ clean ancillary qubits, satisfying
--
--   $$
--   C(|\psi\rangle|0^w\rangle)=(R_\phi|\psi\rangle)|0^w\rangle
--   \quad\text{for every }|\psi\rangle,
--   \qquad |C|\le A2^n n(\kappa+1).
--   $$
--
--   The coefficients vary by coordinate, the exponent is common, the ancilla wires are fixed, and the equality includes global phase. This supplies exact arithmetic reflection synthesis.
--
--   **Formalization Note** The $\kappa+1$ endpoint repair includes basis-vector reflections at $\kappa=0$, which cannot be implemented by a zero-gate circuit. It agrees asymptotically with the printed bound for positive exponents.
-- source:
--   Synthesis of unitaries with Clifford+T circuits, arXiv:1306.3200v1, PDF p. 2, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P12

namespace QAlgorithms.Papers.Independent.Renew46.P12

noncomputable section

/-- Lemma 2, PDF p.2: exact synthesis of a normalized arithmetic reflection, with
one reusable clean workspace qubit. As in Theorem 2, kappa+1 repairs the printed
zero-exponent endpoint: even the reflection about a basis vector is not the identity.
No state-preparation unitary is assumed as a hypothesis. -/
theorem exactReflectionSynthesis :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n → ∀ kappa : ℕ,
      ∀ phi : EuclideanSpace ℂ (Qubits n), IsState phi →
        (∀ i, HasDenominator (Real.sqrt 2) kappa (phi i)) →
      ∃ w : ℕ, w ≤ 1 ∧ ∃ c : Circuit htcxGateSet (n + w),
        ImplementsWithCleanAncillas c.unitary (householderReflection phi) ∧
        (c.size : ℝ) ≤ A * (2 : ℝ) ^ n * (n : ℝ) * ((kappa : ℝ) + 1) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P12
