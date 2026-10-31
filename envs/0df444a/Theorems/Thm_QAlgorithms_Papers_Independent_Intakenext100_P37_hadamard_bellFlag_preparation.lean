-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P37_hadamard_bellFlag_preparation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P37.hadamard_bellFlag_preparation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:23:08.391135+00:00
-- url     : https://prove2.me/theorems/a6d94c73-3e54-433a-b8d6-b3b2c750f89d
-- title:
--   Explicit Hadamard example, Eqs.13–15: Bell flags and preparation
-- statement:
--   Use the normalized Bell vectors $\psi_0=(|00\rangle+|11\rangle)/\sqrt2$, $\psi_1=(|00\rangle-|11\rangle)/\sqrt2$, $\psi_2=(|01\rangle+|10\rangle)/\sqrt2$, and $\psi_3=(|01\rangle-|10\rangle)/\sqrt2$. Write $P_v=|v\rangle\langle v|$ and set
--
--   $$\chi_\pm=\frac{\sqrt{2\pm\sqrt2}|00\rangle\ \pm\sqrt{2\mp\sqrt2}|11\rangle}{2},\qquad \tau_0=\frac{P_{00}+P_{\psi_2}}2,\quad\tau_1=\frac{P_{11}+P_{\psi_3}}2,\quad\tau_2=P_{\chi_+},\quad\tau_3=P_{\chi_-}.$$
--
--   For $p_1=\sqrt2/(1+\sqrt2)$, $p_2=1/(1+\sqrt2)$, and $q=(p_1/2,p_1/2,p_2/2,p_2/2)$, all $q_i$ are nonnegative, their sum is one, all $\psi_i$ are unit vectors, all $\tau_i$ are density matrices, and
--
--   $$\rho_H=\sum_{i=0}^{3}q_i P_{\psi_i}^{AB}\otimes\tau_i^{A'B'}.$$
--
--   Randomly selecting $i$ and separately preparing these two factors therefore prepares $\rho_H$. The product cut here is $AB:A'B'$, and does not assert physical Alice–Bob separability. Eq. (5)'s repeated ket is corrected according to Eqs. (7) and (14).
-- source:
--   Low dimensional bound entanglement with one-way distillable cryptographic key, arXiv:quant-ph/0506203v1, PDF p. 3, Explicit Hadamard example, Eqs.13–15: Bell flags and preparation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P37

noncomputable section

open scoped Matrix BigOperators ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (Key IsPrivate xForm twist twistingMatrix associatedCCQ transposeSecond transposeBob partyCut)

/-- PDF p.3, Eqs.(13)--(15): the exact Bell-flag mixture and normalized
preparation law. Separate preparation refers to AB versus A'B', not Alice versus Bob.
Eq.(5)'s repeated |01> is corrected to |10>, as Eqs.(7),(14) require. -/
theorem hadamard_bellFlag_preparation :
    rhoHadamard = ∑ i : Fin 4, (hadamardWeight i : ℂ) •
      Matrix.kronecker (pureDensity (((![pairKet false 1, pairKet false (-1), pairKet true 1, pairKet true (-1)]) i))) (hadamardFlag i) ∧
    (∀ i, 0 ≤ hadamardWeight i) ∧ (∑ i, hadamardWeight i) = 1 ∧
    (∀ i, ‖((![pairKet false 1, pairKet false (-1), pairKet true 1, pairKet true (-1)]) i)‖ = 1 ∧ IsDensityMatrix (hadamardFlag i)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P37

end
