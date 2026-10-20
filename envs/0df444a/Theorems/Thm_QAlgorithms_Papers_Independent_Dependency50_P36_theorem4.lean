-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P36_theorem4
-- name    : QAlgorithms.Papers.Independent.Dependency50.P36.theorem4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:33:54.232631+00:00
-- url     : https://prove2.me/theorems/6d47e32b-a291-4807-9644-25a0ad402d11
-- title:
--   Exact Hermitian hypothesis-testing characterization
-- statement:
--   Let $\rho$ be a density operator on nonzero finite-dimensional $A\otimes B$, with fixed product bases, and let $0<\varepsilon<1$. For Hermitian $G$, define
--
--   $$\beta_\varepsilon(\rho,G)=\min_{0\le M\le I,\,\operatorname{Tr}(\rho M)\ge1-\varepsilon}\operatorname{Tr}(MG),\qquad D_H^\varepsilon(\rho\|G)=\begin{cases}-\log_2\beta_\varepsilon(\rho,G),&\beta_\varepsilon(\rho,G)>0,\\+\infty,&\beta_\varepsilon(\rho,G)\le0.\end{cases}$$
--
--   The minimum $L=\min_{G=G^\dagger,\,\|G^{T_B}\|_1\le1}D_H^\varepsilon(\rho\|G)$ is finite, nonnegative, and attained. With $\delta=L-\log_2\lfloor2^L\rfloor$,
--
--   $$E_{D,\mathrm{PPT}}^{(1),\varepsilon}(\rho)=L-\delta,\qquad0\le\delta\le1.$$
--
--   Here $\delta$ is the least nonnegative correction making $L-\delta$ the logarithm of a positive integer. PPT means completely PPT-preserving CPTP maps and the one-shot quantity uses squared fidelity to the maximally entangled target. The Hermitian alternative is essential to this exact operational characterization.
-- source:
--   Non-asymptotic entanglement distillation, arXiv:1706.06221v3, PDF p. 6, Seed abstract main result pinned to Theorem 4, Eq. (25): exact hypothesis-testing characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P36

open QAlgorithms.Papers.Independent.Information100.P03 (partialTransposeB)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P63 (testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- Theorem 4, arXiv:1706.06221v3, PDF p.6, Eq.(25).
The minimum is over Hermitian operators, and the integer correction is the least one. -/
theorem theorem4 {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ testingRains rho epsilon = (L : EReal) ∧
      (∃ G : Matrix (A × B) (A × B) ℂ, G.IsHermitian ∧
        traceNorm (partialTransposeB G) ≤ 1 ∧ testingEntropy rho G epsilon = (L : EReal)) ∧
      0 ≤ roundingGap L ∧ roundingGap L ≤ 1 ∧
      oneShot .ppt rho epsilon = (L - roundingGap L : EReal) ∧
      (∀ delta : ℝ, 0 ≤ delta →
        (∃ k : ℕ, 0 < k ∧ L - delta = log2 k) → roundingGap L ≤ delta) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P36

end
