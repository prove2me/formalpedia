-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_boundDominance
-- name    : QAlgorithms.Papers.Independent.Information100.P53.boundDominance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:58:05.720363+00:00
-- url     : https://prove2.me/theorems/c8e70397-ce37-4291-a11f-217e8a3bfe88
-- title:
--   bound-dominance
-- statement:
--   Let $M,N\ge1$, let $\rho_1,\ldots,\rho_M$ be positive semidefinite trace-one operators on $\mathbb C^N$, and fix prior probabilities $p_i\ge0$ with $\sum_i p_i=1$. A decoding POVM $D=(\Lambda_i)$ has positive semidefinite effects summing to the identity. Write $P_c(p,S,D)=\sum_i p_i\operatorname{Tr}(\rho_i\Lambda_i)$, $P_e=1-P_c$, and use an omitted decoder to mean optimization over POVMs alone. Let $F$ denote squared Uhlmann fidelity and $\|A\|_1=\operatorname{Tr}\sqrt{A^\dagger A}$.
--
--   Assume $M\ge2$, and put $X=\sum_{i<j}\|p_i\rho_i-p_j\rho_j\|_1$ and $Y=\sum_{i<j}\sqrt{p_i^2+2(1-2F(\rho_i,\rho_j))p_ip_j+p_j^2}$. Then
--   $$\frac12-\frac{X}{2(M-1)}\le1-\frac1M-\frac XM,\qquad
--   \frac12-\frac{Y}{2(M-1)}\le1-\frac1M-\frac YM.$$
--
--   Thus each new bound dominates its corresponding old bound without an added small-pair-sum hypothesis.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 4, bound-dominance

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.4, comparison after Corollary 2 and footnote 2: each new numerical lower
bound dominates its older counterpart; the pair-sum bound is a conclusion, not an assumption. -/
theorem boundDominance {M N : ℕ} (hM : 2 ≤ M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    (1 / 2 - traceSum p rho / (2 * ((M : ℝ) - 1)) ≤
      1 - 1 / (M : ℝ) - traceSum p rho / (M : ℝ)) ∧
    (1 / 2 - fidelitySum p rho / (2 * ((M : ℝ) - 1)) ≤
      1 - 1 / (M : ℝ) - fidelitySum p rho / (M : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
