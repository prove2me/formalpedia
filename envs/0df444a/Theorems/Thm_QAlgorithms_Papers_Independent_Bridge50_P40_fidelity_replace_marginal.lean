-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_fidelity_replace_marginal
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.fidelity_replace_marginal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:03:59.326242+00:00
-- url     : https://prove2.me/theorems/e1ec7e32-1ed6-4ace-8f51-de624ae94a19
-- title:
--   Replacing a product factor by the actual marginal
-- statement:
--   All registers are finite and nonempty. Density operators have trace one, pure states are normalized, all entropies and logarithms are in base two, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Write $S_a$ for Petz Rényi entropy, with support projection at order zero and the von Neumann limit at order one; $S_\infty(\rho)=-\log_2\lambda_{\max}(\rho)$.
--
--   For density operators $\rho^{AB}$, $\tau^A$, and $\sigma^B$, write $\rho^B=\operatorname{Tr}_A\rho^{AB}$. Then
--
--   $$
--   F(\rho^{AB},\tau^A\otimes\rho^B)\ge\left[F(\rho^{AB},\tau^A\otimes\sigma^B)\right]^2.
--   $$
--
--   No product assumption is imposed on $\rho^{AB}$. Choosing $\tau^A=\operatorname{Tr}_B\rho^{AB}$ gives equation (92) as a direct specialization of this universal statement.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 14, Lemma 16, equation (81)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P40

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply marginalAR)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (cq)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.14--15, Lemma 16, (81): square the RIGHT root fidelity. The actual
B marginal is computed. Equation (92) is the substitution tau=traceRight rho. -/
theorem fidelity_replace_marginal {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (tau : Matrix A A ℂ) (htau : IsDensityMatrix tau)
    (sigma : Matrix B B ℂ) (hsigma : IsDensityMatrix sigma) :
    rootFidelity rho (Matrix.kronecker tau sigma) ^ 2 ≤
      rootFidelity rho (Matrix.kronecker tau (traceLeft rho)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
