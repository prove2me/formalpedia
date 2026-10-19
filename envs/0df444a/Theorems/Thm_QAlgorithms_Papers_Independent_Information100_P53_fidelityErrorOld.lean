-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_fidelityErrorOld
-- name    : QAlgorithms.Papers.Independent.Information100.P53.fidelityErrorOld
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:53:36.767267+00:00
-- url     : https://prove2.me/theorems/d9d35180-0246-4126-954c-8cb377a688b2
-- title:
--   Corollary-1
-- statement:
--   Let $M,N\ge1$, let $\rho_1,\ldots,\rho_M$ be positive semidefinite trace-one operators on $\mathbb C^N$, and fix prior probabilities $p_i\ge0$ with $\sum_i p_i=1$. A decoding POVM $D=(\Lambda_i)$ has positive semidefinite effects summing to the identity. Write $P_c(p,S,D)=\sum_i p_i\operatorname{Tr}(\rho_i\Lambda_i)$, $P_e=1-P_c$, and use an omitted decoder to mean optimization over POVMs alone. Let $F$ denote squared Uhlmann fidelity and $\|A\|_1=\operatorname{Tr}\sqrt{A^\dagger A}$.
--
--   Assume additionally $M\ge2$. Then
--   $$P_e(p,S)\ge\frac12-\frac1{2(M-1)}\sum_{i<j}\sqrt{p_i^2+2(1-2F(\rho_i,\rho_j))p_ip_j+p_j^2}.$$
--
--   This is the fixed-prior fidelity consequence of the older pairwise trace-norm converse.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 3, Corollary-1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.3, Corollary 1, Eq.(4): fixed-prior fidelity lower bound on optimized error.
M ≥ 2 excludes the denominator M−1 = 0. -/
theorem fidelityErrorOld {M N : ℕ} (hM : 2 ≤ M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    1 / 2 - fidelitySum p rho / (2 * ((M : ℝ) - 1)) ≤ 1 - mixedOptSuccess p rho := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
