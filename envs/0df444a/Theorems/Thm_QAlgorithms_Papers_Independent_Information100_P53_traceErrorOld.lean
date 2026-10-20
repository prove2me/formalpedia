-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_traceErrorOld
-- name    : QAlgorithms.Papers.Independent.Information100.P53.traceErrorOld
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:04:32.916857+00:00
-- url     : https://prove2.me/theorems/7396ac55-ecf2-434e-a3a5-2ffcbee303c8
-- title:
--   Theorem 1: Qiu trace-norm error bound
-- statement:
--   Let $M,N\ge1$, let $S=(\rho_i)_{i=1}^M$ consist of positive semidefinite trace-one matrices on $\mathbb C^N$, and fix $p_i\ge0$ with $\sum_i p_i=1$. Write $P_e(p,S)=1-\sup_D\sum_i p_i\operatorname{Tr}(\rho_i\Lambda_i)$, where the supremum ranges over all POVMs $D=(\Lambda_i)_{i=1}^M$. Assume $M\ge2$ and let $\|H\|_1=\operatorname{Tr}|H|$. Then
--
--   $$P_e(p,S)\ge\frac12-\frac{1}{2(M-1)}\sum_{i<j}\|p_i\rho_i-p_j\rho_j\|_1.$$
--
--   This is the cited pairwise converse of Qiu, which the paper compares with its new trace-norm bound.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 3, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.3, Theorem 1 ([7, Theorem 1], Qiu): fixed-prior trace-norm
lower bound on optimized discrimination error. M>=2 is required by M-1.
This is a cited background result; traceNorm has no factor one half. -/
theorem traceErrorOld {M N : ℕ} (hM : 2 ≤ M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    1 / 2 - traceSum p rho / (2 * ((M : ℝ) - 1)) ≤ 1 - mixedOptSuccess p rho := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
