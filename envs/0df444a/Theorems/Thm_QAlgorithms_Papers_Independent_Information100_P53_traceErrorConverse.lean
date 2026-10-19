-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_traceErrorConverse
-- name    : QAlgorithms.Papers.Independent.Information100.P53.traceErrorConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:55:21.229969+00:00
-- url     : https://prove2.me/theorems/f040b92a-4c54-400d-a1e2-7cb720745b35
-- title:
--   Theorem-3
-- statement:
--   Let $M,N\ge1$, let $\rho_1,\ldots,\rho_M$ be positive semidefinite trace-one operators on $\mathbb C^N$, and fix prior probabilities $p_i\ge0$ with $\sum_i p_i=1$. A decoding POVM $D=(\Lambda_i)$ has positive semidefinite effects summing to the identity. Write $P_c(p,S,D)=\sum_i p_i\operatorname{Tr}(\rho_i\Lambda_i)$, $P_e=1-P_c$, and use an omitted decoder to mean optimization over POVMs alone. Let $F$ denote squared Uhlmann fidelity and $\|A\|_1=\operatorname{Tr}\sqrt{A^\dagger A}$.
--
--   Every POVM, and also the optimized discrimination error, satisfies
--   $$P_e(p,S,D)\ge1-\frac1M-\frac1M\sum_{i<j}\|p_i\rho_i-p_j\rho_j\|_1,\qquad
--   P_e(p,S)\ge1-\frac1M-\frac1M\sum_{i<j}\|p_i\rho_i-p_j\rho_j\|_1.$$
--
--   This strengthens the older pairwise error converse, including when the displayed lower bound is negative.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 4, Theorem-3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.4 and Appendix A p.7, Theorem 3: both the advertised arbitrary-POVM
bound and the optimized bound. M=1 is allowed. -/
theorem traceErrorConverse {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    (∀ D : Fin M → Matrix (Fin N) (Fin N) ℂ, IsPOVM D →
      1 - 1 / (M : ℝ) - traceSum p rho / (M : ℝ) ≤ 1 - success p rho D) ∧
    1 - 1 / (M : ℝ) - traceSum p rho / (M : ℝ) ≤ 1 - mixedOptSuccess p rho := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
