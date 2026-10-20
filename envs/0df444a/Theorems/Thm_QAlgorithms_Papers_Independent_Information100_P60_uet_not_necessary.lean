-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_uet_not_necessary
-- name    : QAlgorithms.Papers.Independent.Information100.P60.uet_not_necessary
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:41:56.322205+00:00
-- url     : https://prove2.me/theorems/72b515d3-5998-4c37-a69f-223c7e2d45ed
-- title:
--   Sec.VI A 1, unnumbered: joint UET is strictly stronger than two-unitary cancellation
-- statement:
--   Put $s=\sqrt3$, $K_1=\begin{pmatrix}0&0&(1+is)/2\\0&1&1\\(1-is)/2&1&-1\end{pmatrix}$, and $K_2=\begin{pmatrix}0&0&(s-i)/2\\0&-s&i\\(s+i)/2&-i&s\end{pmatrix}$. Let $\omega=e^{2\pi i/3}$, $F_{jk}=\omega^{jk}/\sqrt3$ for $j,k=0,1,2$, $P=\operatorname{diag}(1,1,\omega)$, $U=PF$, and $V=P^2FPF$. These matrices are traceless Hermitian, $U,V$ are unitary, and $$K_j^T+UK_jU^\dagger+VK_jV^\dagger=0\quad(j=1,2),\qquad\chi(K_1,K_2)=24i.$$ Yet there is no single unitary implementing transpose for both. This is the explicit analytic counterexample to necessity of joint UET.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 24, Sec.VI A 1, unnumbered: joint UET is strictly stronger than two-unitary cancellation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF p.24, Eqs.(73)–(74): explicit analytic counterexample. -/
theorem uet_not_necessary :
    K1.IsHermitian ∧ K2.IsHermitian ∧ K1.trace = 0 ∧ K2.trace = 0 ∧
    counterU * counterUᴴ = 1 ∧ counterUᴴ * counterU = 1 ∧ counterV * counterVᴴ = 1 ∧ counterVᴴ * counterV = 1 ∧
    (∀ M ∈ ({K1, K2} : Set (Mat (Fin 3))), M.transpose + counterU * M * counterUᴴ + counterV * M * counterVᴴ = 0) ∧
    chi K1 K2 = 24 * Complex.I ∧ ¬ JointUET K1 K2 := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
