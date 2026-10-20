-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_fidelityErrorConverse
-- name    : QAlgorithms.Papers.Independent.Information100.P53.fidelityErrorConverse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:57:24.84427+00:00
-- url     : https://prove2.me/theorems/31cd7de1-eb9b-4654-8619-e9b54c6bba68
-- title:
--   Corollary-2
-- statement:
--   Let $M,N\ge1$, let $\rho_1,\ldots,\rho_M$ be positive semidefinite trace-one operators on $\mathbb C^N$, and fix prior probabilities $p_i\ge0$ with $\sum_i p_i=1$. A decoding POVM $D=(\Lambda_i)$ has positive semidefinite effects summing to the identity. Write $P_c(p,S,D)=\sum_i p_i\operatorname{Tr}(\rho_i\Lambda_i)$, $P_e=1-P_c$, and use an omitted decoder to mean optimization over POVMs alone. Let $F$ denote squared Uhlmann fidelity and $\|A\|_1=\operatorname{Tr}\sqrt{A^\dagger A}$.
--
--   Put
--   $$Y=\sum_{i<j}\sqrt{p_i^2+2(1-2F(\rho_i,\rho_j))p_ip_j+p_j^2}.$$
--   For every POVM and for the optimized error,
--   $$P_e(p,S,D)\ge1-\frac1M-\frac YM,\qquad P_e(p,S)\ge1-\frac1M-\frac YM.$$
--
--   This expresses the improved error converse through pairwise fidelities at the original fixed prior.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 4, Corollary-2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.4, Corollary 2, Eq.(6): fixed-prior fidelity error bound for each POVM
and its optimized version. No nonnegativity assumption on the lower bound is added. -/
theorem fidelityErrorConverse {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    (∀ D : Fin M → Matrix (Fin N) (Fin N) ℂ, IsPOVM D →
      1 - 1 / (M : ℝ) - fidelitySum p rho / (M : ℝ) ≤ 1 - success p rho D) ∧
    1 - 1 / (M : ℝ) - fidelitySum p rho / (M : ℝ) ≤ 1 - mixedOptSuccess p rho := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
